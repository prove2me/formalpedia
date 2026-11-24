-- Prove2me | solution 1 for riemann_hypothesis_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T18:50:22.610507+00:00
-- url     : https://prove2.me/submissions/c162b47f-63d9-4576-af11-5f27568ed12c

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_StepanovPolynomial
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
import Theorems.Thm_riemann_hypothesis_stepanov_bound




theorem solution
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
    (f : Polynomial F) (q : ℕ)
    (hq : q = Fintype.card F)
    (hm3 : 3 ≤ f.natDegree)
    (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
        g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
    (hq6m : q > 6 * f.natDegree)
    (hodd : ringChar F ≠ 2) :
    (Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} : ℝ)
      < (q : ℝ) + 4 * (f.natDegree : ℝ) * (Nat.ceil (Real.sqrt q) : ℝ) :=
by
  classical
  set c := (q - 1) / 2 with hc_def
  set m := f.natDegree with hm_def
  have h_stepanov := riemann_hypothesis_stepanov_bound F hF f q 1 hq hm3 hnsq hq6m
  let curveSet := {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f}
  let S1_set := {x : F // x ∈ S_a F f c 1}
  have h_two_S1_bound :
      2 * (Fintype.card S1_set : ℝ) <
        (q : ℝ) + 4 * (m : ℝ) * (Nat.ceil (Real.sqrt q) : ℝ) := by
    simp [hm_def, hc_def, S1_set] at h_stepanov ⊢
    linarith [h_stepanov]
  have h_N_le_2S1 : (Fintype.card curveSet : ℝ) ≤ 2 * (Fintype.card S1_set : ℝ) := by
    have h_proj : ∀ p : curveSet, (p.val.1 : F) ∈ S_a F f c 1 := by
      intro ⟨⟨x, y⟩, hp⟩
      simp [S_a]
      by_cases hfx : Polynomial.eval x f = 0
      · left; exact hfx
      · right
        have hfx_sq : IsSquare (Polynomial.eval x f) :=
          ⟨y, by ring_nf; simpa using hp.symm⟩
        have hfx_ne : Polynomial.eval x f ≠ 0 := hfx
        rw [FiniteField.isSquare_iff hodd hfx_ne] at hfx_sq
        have hcard_eq : Fintype.card F / 2 = (Fintype.card F - 1) / 2 := by
          have hcard_pos : 0 < Fintype.card F := Fintype.card_pos
          have : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two hodd
          omega
        rw [hcard_eq] at hfx_sq
        simpa [hc_def, hq] using hfx_sq
    let proj : curveSet → S1_set := fun p => ⟨p.val.1, h_proj p⟩
    have h_count : Fintype.card curveSet ≤ 2 * Fintype.card S1_set := by
      have h_sigma : Fintype.card curveSet =
          Fintype.card ((y : S1_set) × {x : curveSet // proj x = y}) :=
        Fintype.card_congr (Equiv.sigmaFiberEquiv proj).symm
      rw [h_sigma, Fintype.card_sigma]
      have h_fiber_le : ∀ y : S1_set, Fintype.card {x : curveSet // proj x = y} ≤ 2 := by
        intro ⟨x, hx⟩
        have h_card_sq_roots : Fintype.card {y' : F // y' ^ 2 = Polynomial.eval x f} ≤ 2 := by
          by_cases h0 : Polynomial.eval x f = 0
          · have h_unique : {y' : F // y' ^ 2 = Polynomial.eval x f} ≃ {y' : F // y' = 0} := by
              refine Equiv.subtypeEquiv (Equiv.refl F) ?_
              intro y'
              simp only [Equiv.refl_apply, h0, sq_eq_zero_iff]
            rw [Fintype.card_congr h_unique, Fintype.card_unique]
            norm_num
          · let p : Polynomial F := Polynomial.X ^ 2 - Polynomial.C (Polynomial.eval x f)
            have hp_ne : p ≠ 0 := by
              simp only [p, ne_eq, sub_eq_zero]
              intro h_eq
              have h_deg1 : (Polynomial.X ^ 2 : Polynomial F).natDegree = 2 :=
                Polynomial.natDegree_X_pow 2
              have h_deg2 : (Polynomial.C (Polynomial.eval x f) : Polynomial F).natDegree = 0 :=
                Polynomial.natDegree_C _
              have : (2 : ℕ) = 0 := by rw [← h_deg1, h_eq, h_deg2]
              norm_num at this
            have h_deg : p.natDegree ≤ 2 := by
              simp only [p]
              calc (Polynomial.X ^ 2 - Polynomial.C (Polynomial.eval x f)).natDegree
                  ≤ max (Polynomial.X ^ 2 : Polynomial F).natDegree
                      (Polynomial.C (Polynomial.eval x f)).natDegree :=
                    Polynomial.natDegree_sub_le _ _
                _ = max 2 0 := by simp [Polynomial.natDegree_C]
                _ = 2 := by norm_num
            have h_roots : ∀ y' : F, p.IsRoot y' ↔ y' ^ 2 = Polynomial.eval x f := by
              intro y'
              simp only [p, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
                Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero]
            have h_card_roots : Multiset.card p.roots ≤ p.natDegree := Polynomial.card_roots' p
            have h_inj : Function.Injective (fun (y' : {y' : F // y' ^ 2 = Polynomial.eval x f}) =>
                (⟨y'.val, (Polynomial.mem_roots hp_ne).mpr ((h_roots y'.val).mpr y'.property)⟩ :
                  {y' : F // y' ∈ p.roots})) := by
              intro ⟨a, ha⟩ ⟨b, hb⟩ h
              simp only [Subtype.mk.injEq] at h
              exact Subtype.ext h
            have h_card_le_roots : Fintype.card {y' : F // y' ^ 2 = Polynomial.eval x f} ≤
                Fintype.card {y' : F // y' ∈ p.roots} := Fintype.card_le_of_injective _ h_inj
            have h_fintype_le_multiset :
                Fintype.card {y' : F // y' ∈ p.roots} ≤ Multiset.card p.roots := by
              calc Fintype.card {y' : F // y' ∈ p.roots}
                  ≤ Fintype.card p.roots.toFinset := by
                    refine Fintype.card_le_of_injective
                      (fun ⟨y', hy'⟩ => ⟨y', Multiset.mem_toFinset.mpr hy'⟩) ?_
                    intro ⟨a, ha⟩ ⟨b, hb⟩ h
                    simp only [Subtype.mk.injEq] at h
                    exact Subtype.ext h
                _ = p.roots.toFinset.card := Fintype.card_coe p.roots.toFinset
                _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le p.roots
            calc Fintype.card {y' : F // y' ^ 2 = Polynomial.eval x f}
                ≤ Fintype.card {y' : F // y' ∈ p.roots} := h_card_le_roots
              _ ≤ Multiset.card p.roots := h_fintype_le_multiset
              _ ≤ p.natDegree := h_card_roots
              _ ≤ 2 := h_deg
        have h_fiber_inj : Function.Injective (fun (p' : {p' : curveSet // proj p' = ⟨x, hx⟩}) =>
            (⟨p'.val.val.2, by
              have hp := p'.val.property
              have hpx : proj p'.val = ⟨x, hx⟩ := p'.property
              simp only [proj] at hpx
              have hx_eq : p'.val.val.1 = x := Subtype.ext_iff.mp hpx
              simp only [hx_eq] at hp
              exact hp⟩ : {y' : F // y' ^ 2 = Polynomial.eval x f})) := by
          intro ⟨⟨⟨x1, y1⟩, hp1⟩, hproj1⟩ ⟨⟨⟨x2, y2⟩, hp2⟩, hproj2⟩ h
          simp only [Subtype.mk.injEq] at h
          simp only [proj] at hproj1 hproj2
          have hx1_eq : x1 = x := Subtype.ext_iff.mp hproj1
          have hx2_eq : x2 = x := Subtype.ext_iff.mp hproj2
          simp only [Subtype.mk.injEq]
          refine Subtype.ext ?_
          simp only [Prod.mk.injEq]
          exact ⟨hx1_eq.trans hx2_eq.symm, h⟩
        exact le_trans (Fintype.card_le_of_injective _ h_fiber_inj) h_card_sq_roots
      calc ∑ y : S1_set, Fintype.card {x : curveSet // proj x = y}
          ≤ ∑ _ : S1_set, 2 := Finset.sum_le_sum (fun y _ => h_fiber_le y)
        _ = 2 * Fintype.card S1_set := by simp [Finset.sum_const, Finset.card_univ]; ring
    exact_mod_cast h_count
  have h := lt_of_le_of_lt h_N_le_2S1 h_two_S1_bound
  simpa [curveSet, S1_set, hc_def, hm_def] using h
