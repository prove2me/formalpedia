-- Prove2me | solution 1 for riemann_hypothesis_hec
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-25T06:47:58.985649+00:00
-- url     : https://prove2.me/submissions/664c5f5f-3990-43e4-ae14-e86434e0d427

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
import Theorems.Thm_curve_count_ge_two_times_N1
import Theorems.Thm_partition_N1_eq_q_sub_S_neg1
import Theorems.Thm_riemann_hypothesis_stepanov_bound
import Theorems.Thm_riemann_hypothesis_upper_bound

section
















lemma riemann_hypothesis_lower_bound
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
    (f : Polynomial F) (q : ℕ)
    (hq : q = Fintype.card F)
    (hm3 : 3 ≤ f.natDegree)
    (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
        g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
    (hq6m : q > 6 * f.natDegree)
    (hodd : ringChar F ≠ 2) :
    (Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} : ℝ)
      > (q : ℝ) - 4 * (f.natDegree : ℝ) * (Nat.ceil (Real.sqrt q) : ℝ) :=
by
  classical
  linarith [ curve_count_ge_two_times_N1 F f q hq hodd,
            partition_N1_eq_q_sub_S_neg1 F f q hq hodd,
            riemann_hypothesis_stepanov_bound F hF f q (-1) hq hm3 hnsq hq6m ]





end



theorem solution
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (f : Polynomial F) (q : ℕ)
    (hq : q = Fintype.card F)
    (hm3 : 3 ≤ f.natDegree)
    (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
        g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
    (hq6m : q > 6 * f.natDegree) :
    |((q : ℝ) - (Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} : ℝ))|
      < (5 : ℝ) * (f.natDegree : ℝ) * Real.sqrt (q : ℝ) :=
by
  have hm_pos : (0 : ℝ) < (f.natDegree : ℝ) :=
    Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by norm_num) hm3)
  have hq_pos : (0 : ℝ) < (q : ℝ) :=
    Nat.cast_pos.mpr
      (Nat.lt_trans (Nat.mul_pos (by norm_num)
        (Nat.lt_of_lt_of_le (by norm_num) hm3)) hq6m)
  by_cases hchar2 : ringChar F = 2
  · have hN_eq_q :
        Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} = q := by
      haveI : CharP F 2 := hchar2 ▸ ringChar.charP F
      haveI : ExpChar F 2 := .prime Nat.prime_two
      let frob := frobeniusEquiv F 2
      simpa [hq] using
        (Fintype.card_congr {
          toFun := fun ⟨⟨x, _⟩, _⟩ => x
          invFun := fun x => ⟨(x, frob.symm (Polynomial.eval x f)), frob.apply_symm_apply _⟩
          left_inv := fun ⟨⟨_, _⟩, hy⟩ =>
            Subtype.ext (Prod.ext rfl (frob.injective
              (by
                simp only [frobeniusEquiv_def, hy, frob,
                  RingEquiv.apply_symm_apply])))
          right_inv := fun _ => rfl
        })
    simp [hN_eq_q, sub_self, abs_zero]
    positivity
  · set N : ℝ :=
      (Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} : ℝ)
    have h_abs :
        |(q : ℝ) - N| <
          4 * (f.natDegree : ℝ) * (Nat.ceil (Real.sqrt q) : ℝ) := by
      have h_upper :=
        riemann_hypothesis_upper_bound F hchar2 f q hq hm3 hnsq hq6m hchar2
      have h_lower :=
        riemann_hypothesis_lower_bound F hchar2 f q hq hm3 hnsq hq6m hchar2
      rw [abs_sub_lt_iff]; constructor <;> linarith
    have h_ceil_bound : (Nat.ceil (Real.sqrt q) : ℝ) ≤ Real.sqrt q + 1 := by
      have := Nat.ceil_lt_add_one (Real.sqrt_nonneg q)
      linarith
    have h_q_ge_18 : (18 : ℕ) ≤ q := by
      have : 6 * 3 ≤ 6 * f.natDegree := Nat.mul_le_mul_left 6 hm3
      omega
    have h_sqrt_gt_4 : (4 : ℝ) < Real.sqrt q := by
      rw [show (4 : ℝ) = Real.sqrt 16 by symm; apply (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2; norm_num]
      apply Real.sqrt_lt_sqrt (by norm_num)
      exact_mod_cast Nat.lt_of_lt_of_le (by norm_num : 16 < 18) h_q_ge_18
    calc
      |(q : ℝ) - N| <
          4 * (f.natDegree : ℝ) * (Nat.ceil (Real.sqrt q) : ℝ) := h_abs
      _ ≤ 4 * (f.natDegree : ℝ) * (Real.sqrt q + 1) := by
        nlinarith [h_ceil_bound]
      _ = 4 * (f.natDegree : ℝ) * Real.sqrt q +
            4 * (f.natDegree : ℝ) := by ring
      _ < 4 * (f.natDegree : ℝ) * Real.sqrt q +
            (f.natDegree : ℝ) * Real.sqrt q := by
        nlinarith [hm_pos, h_sqrt_gt_4]
      _ = 5 * (f.natDegree : ℝ) * Real.sqrt q := by ring
