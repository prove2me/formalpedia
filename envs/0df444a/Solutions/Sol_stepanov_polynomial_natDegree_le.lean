-- Prove2me | solution 1 for stepanov_polynomial_natDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T15:35:52.269967+00:00
-- url     : https://prove2.me/submissions/4043a50a-3f8e-403c-acf5-da75ecb4c194

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




theorem solution (F : Type*) [Field F] [Fintype F] (f : Polynomial F)
  (q m ℓ c d J : ℕ) (hfdeg : f.natDegree = m) (rj sj : ℕ → Polynomial F)
  (hdegr : ∀ j < J, (rj j).natDegree ≤ d) (hdegs : ∀ j < J, (sj j).natDegree ≤ d) :
  (f^ℓ * (Finset.sum (Finset.range J)
    (fun j => ((rj j) + (sj j) * f^c) * Polynomial.X^(j*q)))).natDegree
      ≤ ℓ * m + d + c * m + (J - 1) * q :=
by
  let fsum : ℕ → Polynomial F :=
    fun j => ((rj j) + (sj j) * f ^ c) * Polynomial.X ^ (j * q)
  have h_fsum_deg : ∀ j < J, (fsum j).natDegree ≤ d + c * m + j * q := by
    intro j hj
    have hdeg_sj_fc : ((sj j) * f ^ c).natDegree ≤ d + c * m :=
      (Polynomial.natDegree_mul_le (p := sj j) (q := f ^ c)).trans
        (Nat.add_le_add (hdegs j hj) (by simp [hfdeg]))
    have hdeg_sum : ((rj j) + (sj j) * f ^ c).natDegree ≤ d + c * m :=
      (Polynomial.natDegree_add_le (p := rj j) (q := (sj j) * f ^ c)).trans
        (max_le_iff.2
          ⟨(hdegr j hj).trans (Nat.le_add_right _ _), hdeg_sj_fc⟩)
    have hmul :
        (((rj j) + (sj j) * f ^ c) * Polynomial.X ^ (j * q)).natDegree ≤
          d + c * m + j * q :=
      (Polynomial.natDegree_mul_le
        (p := (rj j) + (sj j) * f ^ c)
        (q := Polynomial.X ^ (j * q))).trans
        (by
          have := Nat.add_le_add_right hdeg_sum (j * q)
          simpa [Polynomial.natDegree_X_pow (j * q)] using this)
    simpa [fsum] using hmul
  have h_sum_deg :
      (Finset.sum (Finset.range J) fsum).natDegree ≤ d + c * m + (J - 1) * q := by
    refine
      Polynomial.natDegree_sum_le_of_forall_le
        (s := Finset.range J) (f := fsum)
        (n := d + c * m + (J - 1) * q) ?_
    intro j hj
    have hj_lt : j < J := Finset.mem_range.mp hj
    exact
      (h_fsum_deg j hj_lt).trans
        (Nat.add_le_add_left
          (Nat.mul_le_mul_right _ (Nat.le_pred_of_lt hj_lt)) _)
  have h_total :
      (f ^ ℓ * Finset.sum (Finset.range J) fsum).natDegree ≤
        ℓ * m + (d + c * m + (J - 1) * q) := by
    have hdeg_fℓ : (f ^ ℓ : Polynomial F).natDegree ≤ ℓ * m := by
      simp [hfdeg]
    exact
      (Polynomial.natDegree_mul_le
        (p := f ^ ℓ)
        (q := Finset.sum (Finset.range J) fsum)).trans
        (Nat.add_le_add hdeg_fℓ h_sum_deg)
  have h_rhs : ℓ * m + (d + c * m + (J - 1) * q) =
      ℓ * m + d + c * m + (J - 1) * q := by
    ac_rfl
  simpa [fsum, h_rhs] using h_total
