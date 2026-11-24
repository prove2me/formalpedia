-- Prove2me | solution 1 for curve_count_ge_two_times_N1
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T14:18:28.698704+00:00
-- url     : https://prove2.me/submissions/cf89eba0-0d4e-484b-ad68-0cbf50500552

import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring




theorem solution
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (f : Polynomial F) (q : ℕ)
    (hq : q = Fintype.card F)
    (hodd : ringChar F ≠ 2) :
    (Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} : ℝ)
      ≥
        2 *
          (Fintype.card
              {x : F // (Polynomial.eval x f) ^ ((q - 1) / 2) = 1 ∧
                Polynomial.eval x f ≠ 0} : ℝ) :=
by
  classical
  subst hq
  set c := (Fintype.card F - 1) / 2 with hc_def
  let N1 := {x : F // (Polynomial.eval x f) ^ c = 1 ∧ Polynomial.eval x f ≠ 0}
  let C := {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f}
  let C_from_N1 :=
    {p : C // p.val.1 ∈ {x : F | (Polynomial.eval x f) ^ c = 1 ∧ Polynomial.eval x f ≠ 0}}
  have h1 : Fintype.card C ≥ Fintype.card C_from_N1 :=
    Fintype.card_le_of_embedding (Function.Embedding.subtype _)
  have hcard_div : Fintype.card F / 2 = (Fintype.card F - 1) / 2 := by
    have _ := FiniteField.odd_card_of_char_ne_two hodd
    have _ : 0 < Fintype.card F := Fintype.card_pos
    omega
  have h2 : Fintype.card C_from_N1 = 2 * Fintype.card N1 := by
    let proj : C_from_N1 → N1 := fun ⟨⟨⟨x, y⟩, hp⟩, hx⟩ => ⟨x, hx⟩
    have h_fiber_card : ∀ x : N1, Fintype.card {p : C_from_N1 // proj p = x} = 2 := by
      intro ⟨x, ⟨hxc, hx_ne⟩⟩
      have hfx_ne : Polynomial.eval x f ≠ 0 := hx_ne
      have h_euler := FiniteField.isSquare_iff hodd hfx_ne
      rw [hcard_div] at h_euler
      have hfx_sq : IsSquare (Polynomial.eval x f) := h_euler.mpr hxc
      obtain ⟨r, hr⟩ := hfx_sq.exists_mul_self
      have hr' : r ^ 2 = Polynomial.eval x f := by rw [sq]; exact hr.symm
      have hr_ne : r ≠ 0 := by
        intro h; rw [h, sq, mul_zero] at hr'; exact hfx_ne hr'.symm
      have h_roots : ∀ y : F, y ^ 2 = Polynomial.eval x f ↔ y = r ∨ y = -r := by
        intro y
        constructor
        · intro hy
          have : y ^ 2 = r ^ 2 := by
            simpa [hr'.symm] using hy
          rw [sq_eq_sq_iff_eq_or_eq_neg] at this
          exact this
        · intro h_or
          cases h_or with
          | inl h => rw [h, hr']
          | inr h => rw [h, neg_sq, hr']
      have hr_ne_neg : r ≠ -r := by
        intro h
        have h2r : r + r = 0 := by
          have : r - (-r) = 0 := sub_eq_zero.mpr h
          simp only [sub_neg_eq_add] at this
          exact this
        have h2_times_r : (2 : F) * r = 0 := by rw [two_mul]; exact h2r
        rw [mul_eq_zero] at h2_times_r
        cases h2_times_r with
        | inl h2 =>
          have := CharP.ringChar_of_prime_eq_zero (R := F) Nat.prime_two h2
          exact hodd this
        | inr h0 => exact hr_ne h0
      have h_sq_roots : Fintype.card {y : F // y ^ 2 = Polynomial.eval x f} = 2 := by
        have h_equiv : {y : F // y ^ 2 = Polynomial.eval x f} ≃ ({r, -r} : Finset F) := by
          refine {
            toFun := fun ⟨y, hy⟩ => by
              have hy_or := (h_roots y).mp hy
              refine ⟨y, ?_⟩
              simp only [Finset.mem_insert, Finset.mem_singleton]
              exact hy_or
            invFun := fun ⟨y, hy⟩ => by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hy
              refine ⟨y, (h_roots y).mpr hy⟩
            left_inv := fun ⟨y, hy⟩ => by simp
            right_inv := fun ⟨y, hy⟩ => by simp
          }
        rw [Fintype.card_congr h_equiv]
        have : ({r, -r} : Finset F).card = 2 := by
          rw [Finset.card_insert_of_notMem, Finset.card_singleton]
          simp only [Finset.mem_singleton]
          exact hr_ne_neg
        simp only [Fintype.card_coe]
        exact this
      have h_fiber_equiv : {p : C_from_N1 // proj p = ⟨x, ⟨hxc, hx_ne⟩⟩} ≃
          {y : F // y ^ 2 = Polynomial.eval x f} := by
        refine {
          toFun := fun ⟨⟨⟨⟨x', y⟩, hp⟩, hx'⟩, hproj⟩ => by
            simp only [proj] at hproj
            have hx'_eq : x' = x := Subtype.ext_iff.mp hproj
            exact ⟨y, by simp only [← hx'_eq]; exact hp⟩
          invFun := fun ⟨y, hy⟩ => by
            refine ⟨⟨⟨⟨x, y⟩, hy⟩, ?_⟩, rfl⟩
            simp only [Set.mem_setOf_eq]
            exact ⟨hxc, hx_ne⟩
          left_inv := by
            intro ⟨⟨⟨⟨x', y⟩, hp⟩, hx'⟩, hproj⟩
            simp only [proj] at hproj
            have hx'_eq : x' = x := Subtype.ext_iff.mp hproj
            simp only [Subtype.mk.injEq]
            subst hx'_eq
            rfl
          right_inv := fun ⟨y, hy⟩ => rfl
        }
      rw [Fintype.card_congr h_fiber_equiv, h_sq_roots]
    calc
      Fintype.card C_from_N1
          = Fintype.card ((x : N1) × {p : C_from_N1 // proj p = x}) := by
            exact Fintype.card_congr (Equiv.sigmaFiberEquiv proj).symm
      _ = ∑ x : N1, Fintype.card {p : C_from_N1 // proj p = x} := Fintype.card_sigma
      _ = ∑ _x : N1, 2 := by
          refine Finset.sum_congr rfl ?_
          intro x _
          exact h_fiber_card x
      _ = 2 * Fintype.card N1 := by
          simp [Finset.sum_const, Finset.card_univ, mul_comm]
  have h3 : (Fintype.card C : ℝ) ≥ 2 * (Fintype.card N1 : ℝ) := by
    have h3' : (Fintype.card C : ℝ) ≥ (Fintype.card C_from_N1 : ℝ) := by exact_mod_cast h1
    simpa [h2, Nat.cast_mul] using h3'
  simpa [C, N1, hc_def] using h3
