-- Prove2me | solution 1 for hasse_vanishing_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T14:55:03.679053+00:00
-- url     : https://prove2.me/submissions/3d22615a-7c1d-4eed-988c-e3586991c497

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_HasseDerivatives
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
import Theorems.Thm_hasse_divisibility




theorem solution
  (F : Type*) [Field F] [DecidableEq F]
  (r : Polynomial F) (ℓ : ℕ)
  (S : Finset F)
  (hr : r ≠ 0)
  (hℓ_pos : 0 < ℓ)
  (hvan : ∀ x ∈ S, ∀ k < ℓ, (hasseDerivOp F k r).eval x = 0) :
  (S.card : ℝ) ≤ (r.natDegree : ℝ) / ℓ :=
by
  let s : F → Polynomial F := fun x => (Polynomial.X - Polynomial.C x) ^ ℓ
  have hpair_all : Pairwise fun x y : F => IsCoprime (s x) (s y) := by
    have hlin :
        Pairwise fun x y : F =>
          IsCoprime (Polynomial.X - Polynomial.C x)
            (Polynomial.X - Polynomial.C y) := by
      simpa [Function.onFun] using
        (Polynomial.pairwise_coprime_X_sub_C (K := F)
          (s := fun x : F => x) (H := fun {x} {y} h => h))
    exact hlin.mono fun x y hcop => by
      simpa [s] using (IsCoprime.pow hcop : _)
  have hprod_dvd : (∏ x ∈ S, s x) ∣ r := by
    refine
      Finset.prod_dvd_of_coprime (t := S) (s := s) (z := r) ?_ ?_
    · intro x hx y hy hxy
      simpa [Function.onFun] using hpair_all hxy
    · intro x hx
      simpa [s] using
        hasse_divisibility (F := F) (f := r) (a := x) (ℓ := ℓ) (hvan x hx)
  have hP_nat_eq :
      ((∏ x ∈ S, s x : Polynomial F).natDegree) = S.card * ℓ := by
    calc
      ((∏ x ∈ S, s x : Polynomial F).natDegree)
          = ∑ x ∈ S, (s x).natDegree := by
              simpa using
                (Polynomial.natDegree_prod_of_monic (s := S) (f := s)
                  (by
                    intro x hx
                    simpa [s] using (Polynomial.monic_X_sub_C x).pow ℓ))
      _ = ∑ x ∈ S, ℓ := by
            simp [s]
      _ = S.card * ℓ := by simp
  have h_nat' : S.card * ℓ ≤ r.natDegree := by
    have hnat_le :
        ((∏ x ∈ S, s x : Polynomial F).natDegree) ≤ r.natDegree :=
      (Polynomial.natDegree_le_iff_degree_le).2
        ((Polynomial.degree_le_of_dvd
            (p := ∏ x ∈ S, s x) (q := r) hprod_dvd hr).trans
          (Polynomial.degree_le_natDegree (p := r)))
    simpa [hP_nat_eq] using hnat_le
  have hℓ_pos' : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ_pos
  have h_real_mul : (S.card : ℝ) * (ℓ : ℝ) ≤ (r.natDegree : ℝ) := by
    exact_mod_cast h_nat'
  have hne : (ℓ : ℝ) ≠ 0 := ne_of_gt hℓ_pos'
  simpa [mul_comm, mul_left_comm, mul_assoc, hne, div_eq_mul_inv] using
    (mul_le_mul_of_nonneg_right h_real_mul (inv_nonneg.mpr hℓ_pos'.le))
