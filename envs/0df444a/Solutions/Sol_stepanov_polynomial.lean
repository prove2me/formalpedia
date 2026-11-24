-- Prove2me | solution 1 for stepanov_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T17:45:53.427305+00:00
-- url     : https://prove2.me/submissions/d2b4fc6c-14d4-4eae-a1a6-bec1087b5a33

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_HasseDerivatives
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
import Theorems.Thm_stepanov_nonzero
import Theorems.Thm_stepanov_polynomial_natDegree_le
import Theorems.Thm_stepanov_system_has_solution
import Theorems.Thm_stepanov_vanishing_nonzeros

section


lemma stepanov_vanishing_roots (F : Type*) [Field F] (f g : Polynomial F) (ℓ : ℕ) (x : F)
  (hx : Polynomial.eval x f = 0) :
  ∀ k < ℓ, (hasseDerivOp F k (f ^ ℓ * g)).eval x = 0 :=
by
  intro k hk
  rcases hasseDerivOp_mul_pow_dvd F k ℓ g f with ⟨Q, hQ⟩
  simp [mul_comm, hQ, hx, zero_pow (Nat.sub_ne_zero_of_lt hk)]



end

section




































lemma stepanov_constructed_nonzero
  (F : Type*) [Field F] [Fintype F] (hF : ringChar F ≠ 2)
  (f : Polynomial F) (q m ℓ J c d : ℕ)
  (hq : q = Fintype.card F) (hfdeg : f.natDegree = m) (hc : c = (q - 1) / 2)
  (hm_pos : 0 < m)
  (hq6m : q > 6 * m)
  (hd : d = Nat.ceil (((q : ℚ) - m) / 2) - 1)
  (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
      g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
  (rj sj : ℕ → Polynomial F)
  (hdeg : ∀ j < J, (rj j).natDegree ≤ d ∧ (sj j).natDegree ≤ d)
  (hnz : ∃ j < J, rj j ≠ 0 ∨ sj j ≠ 0) :
  f^ℓ * (Finset.sum (Finset.range J)
    (fun j => ((rj j) + (sj j) * f^c) * (Polynomial.X)^(j*q))) ≠ 0 :=
by
  intro hz
  have hzero :=
    (stepanov_nonzero F hF f q m ℓ J c hc hq hfdeg hm_pos hq6m rj sj hnsq
      (by simpa [hd] using hdeg)).1 hz
  rcases hnz with ⟨j, hj, h_or⟩
  exact h_or.elim (· (hzero j hj).1) (· (hzero j hj).2)

end



theorem solution
  (F : Type*) [Field F] [Fintype F] (hF : ringChar F ≠ 2)
  (f : Polynomial F) (q ℓ : ℕ) (a : F)
  (hq : q = Fintype.card F) (hm3 : 3 ≤ f.natDegree)
  (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
      g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
  (hq6m : q > 6 * f.natDegree) (hℓ_pos : 0 < ℓ) (hl : ℓ ≤ q / 3) :
  ∃ r : Polynomial F,
    r ≠ 0 ∧
    ((r.natDegree : ℝ) <
      ((f.natDegree * q : ℕ) : ℝ) +
        ((ℓ * q : ℕ) : ℝ) / 2 +
        ((ℓ * ℓ * f.natDegree : ℕ) : ℝ)) ∧
    (∀ x ∈ S_a F f ((q - 1) / 2) a, ∀ k < ℓ, (hasseDerivOp F k r).eval x = 0) :=
by
  set m : ℕ := f.natDegree with hm_def
  have hfdeg : f.natDegree = m := by simp [hm_def]
  have hm3' : 3 ≤ m := by simpa [hm_def] using hm3
  have hm_pos : 0 < m := lt_of_lt_of_le (by decide : 0 < 3) hm3'
  have hm_ge_two : 2 ≤ m := le_trans (by decide : 2 ≤ 3) hm3'
  have h6mq : 6 * m < q := by simpa [hm_def] using hq6m
  have hq_pos_nat : 0 < q := lt_of_le_of_lt (Nat.zero_le _) h6mq
  let c : ℕ := (q - 1) / 2
  have hc : c = (q - 1) / 2 := rfl
  let d : ℕ := Nat.ceil (((q : ℚ) - m) / 2) - 1
  have hd : d = Nat.ceil (((q : ℚ) - m) / 2) - 1 := rfl
  set Jreal : ℚ := (ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ) with hJreal_def
  set J : ℕ := Nat.ceil Jreal with hJ_def
  have hJ_expr_pos :
      0 < (ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ) := by
    have hhalf_pos : (0 : ℚ) < (ℓ : ℚ) / 2 :=
      div_pos (by exact_mod_cast hℓ_pos) (by norm_num)
    have hdiv_nonneg :
        (0 : ℚ) ≤ (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ) :=
      div_nonneg
        (mul_nonneg (pow_two_nonneg _) (by exact_mod_cast (Nat.zero_le m)))
        (le_of_lt (by exact_mod_cast hq_pos_nat))
    exact add_pos_of_pos_of_nonneg hhalf_pos hdiv_nonneg
  have hJ_pos :
      1 ≤ Nat.ceil ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ)) :=
    Nat.one_le_ceil_iff.mpr hJ_expr_pos
  have h_system' :
      ∃ rj sj : ℕ → Polynomial F,
        (∃ j < J, rj j ≠ 0 ∨ sj j ≠ 0) ∧
        (∀ j < J, (rj j).natDegree ≤ d ∧ (sj j).natDegree ≤ d) ∧
        (∀ x : F, f.eval x ≠ 0 → (f.eval x) ^ c = a →
          ∀ k < ℓ,
            Finset.sum (Finset.range J)
              (fun j =>
                (((hasseDerivOp F k (f ^ ℓ * rj j)) / f ^ (ℓ - k)).eval x +
                    a *
                      ((hasseDerivOp F k (f ^ (ℓ + c) * sj j)) /
                          f ^ (ℓ + c - k)).eval x) *
                  x ^ j) = 0) := by
    simpa [d, hd, J, hJ_def, Jreal, hJreal_def, c, hc] using
      (stepanov_system_has_solution
        (F := F) (f := f) (q := q) (m := m) (ℓ := ℓ) (a := a)
        hq hfdeg hm_ge_two hm_pos hℓ_pos (by simpa [hm_def] using hq6m) hl hJ_pos)
  rcases h_system' with ⟨rj, sj, hnz, hdeg, hvan⟩
  set R : Polynomial F :=
    f ^ ℓ *
      Finset.sum (Finset.range J)
        (fun j => ((rj j) + (sj j) * f ^ c) * Polynomial.X ^ (j * q)) with hR_def
  have hdegr : ∀ j < J, (rj j).natDegree ≤ d := fun j hj => (hdeg j hj).1
  have hdegs : ∀ j < J, (sj j).natDegree ≤ d := fun j hj => (hdeg j hj).2
  have hR_ne_zero : R ≠ 0 := by
    simpa [R, hR_def] using
      (stepanov_constructed_nonzero
        (F := F) (hF := hF) (f := f) (q := q) (m := m) (ℓ := ℓ)
        (J := J) (c := c) (d := d)
        hq hfdeg hc hm_pos (by simpa [hm_def] using hq6m) hd hnsq rj sj (by
          intro j hj; exact ⟨hdegr j hj, hdegs j hj⟩) hnz)
  have hdeg_nat_le :
      R.natDegree ≤ ℓ * m + d + c * m + (J - 1) * q := by
    simpa [R, hR_def] using
      (stepanov_polynomial_natDegree_le
        (F := F) (f := f) (q := q) (m := m) (ℓ := ℓ)
        (c := c) (d := d) (J := J)
        hfdeg rj sj hdegr hdegs)
  let Jm1 : ℕ := J - 1
  have hdeg_le_coreJ :
      (R.natDegree : ℚ)
        ≤ (ℓ : ℚ) * (m : ℚ) + (d : ℚ) + (c : ℚ) * (m : ℚ)
          + (Jm1 : ℚ) * (q : ℚ) := by
    have : (R.natDegree : ℚ) ≤ ((ℓ * m + d + c * m + Jm1 * q : ℕ) : ℚ) := by
      exact_mod_cast (by simpa [Jm1] using hdeg_nat_le)
    simpa [Nat.cast_add, Nat.cast_mul] using this
  set core : ℚ := (ℓ : ℚ) * (m : ℚ) + (d : ℚ) + (c : ℚ) * (m : ℚ) with hcore_def
  have hdeg_core_le :
      (R.natDegree : ℚ) ≤ core + (Jm1 : ℚ) * (q : ℚ) := by
    simpa [core, add_assoc] using hdeg_le_coreJ
  have hq_pos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq_pos_nat
  have hm_pos' : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm_pos
  have hℓ_le_q_div3 : (ℓ : ℚ) ≤ (q : ℚ) / 3 := by
    have h1 : (ℓ : ℚ) ≤ ((q / 3 : ℕ) : ℚ) := by exact_mod_cast hl
    exact le_trans h1 (by simpa using (Nat.cast_div_le (α := ℚ) (m := q) (n := 3)))
  have hℓm_le : (ℓ : ℚ) * (m : ℚ) ≤ (q : ℚ) / 3 * (m : ℚ) :=
    mul_le_mul_of_nonneg_right hℓ_le_q_div3 (le_of_lt hm_pos')
  have hx1_le_hx2 : (((q : ℚ) - (m : ℚ)) / 2) ≤ (q : ℚ) / 2 := by
    simpa [sub_eq_add_neg] using
      (div_le_div_of_nonneg_right
        (sub_le_self _ (by exact_mod_cast (Nat.zero_le m))) (by norm_num))
  have hceil_le :
      Nat.ceil (((q : ℚ) - (m : ℚ)) / 2)
        ≤ Nat.ceil ((q : ℚ) / 2) :=
    Nat.ceil_le_ceil hx1_le_hx2
  have hd_le_ceil_x1 :
      d ≤ Nat.ceil (((q : ℚ) - (m : ℚ)) / 2) := by
    simp [hd]
  have hd_le_ceil_x2 : d ≤ Nat.ceil ((q : ℚ) / 2) :=
    le_trans hd_le_ceil_x1 hceil_le
  have hd_le : (d : ℚ) ≤ (q : ℚ) / 2 + 1 := by
    have hx2_nonneg : (0 : ℚ) ≤ (q : ℚ) / 2 :=
      div_nonneg (le_of_lt hq_pos) (by norm_num)
    exact le_trans (by exact_mod_cast hd_le_ceil_x2)
      (le_of_lt (Nat.ceil_lt_add_one hx2_nonneg))
  have h2c_le_q1_nat : 2 * c ≤ q - 1 := by
    simpa [c, hc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Nat.div_mul_le_self (q - 1) 2)
  have h2c_le_q1 : (2 : ℚ) * (c : ℚ) ≤ (q : ℚ) - 1 := by
    have hq_ge_one : 1 ≤ q := Nat.succ_le_of_lt hq_pos_nat
    simpa [Nat.cast_mul, Nat.cast_sub hq_ge_one, mul_comm, mul_left_comm, mul_assoc] using
      (show ((2 * c : ℕ) : ℚ) ≤ ((q - 1 : ℕ) : ℚ) from by exact_mod_cast h2c_le_q1_nat)
  have hc_le : (c : ℚ) ≤ ((q : ℚ) - 1) / 2 := by
    have h2_pos : (0 : ℚ) < (2 : ℚ) := by norm_num
    have hq1_eq' :
        (2 : ℚ) * (((q : ℚ) - 1) / 2) = (q : ℚ) - 1 := by
      simp [div_eq_mul_inv, mul_comm, mul_left_comm,
        (two_ne_zero : (2 : ℚ) ≠ 0)]
    have h2c_le : (2 : ℚ) * (c : ℚ)
        ≤ (2 : ℚ) * (((q : ℚ) - 1) / 2) := by
      simpa [hq1_eq'] using h2c_le_q1
    exact (le_of_mul_le_mul_left h2c_le h2_pos)
  have hcm_le : (c : ℚ) * (m : ℚ)
      ≤ ((q : ℚ) - 1) / 2 * (m : ℚ) :=
    mul_le_mul_of_nonneg_right hc_le (le_of_lt hm_pos')
  have h_d_add_c :
      (d : ℚ) + (c : ℚ) * (m : ℚ)
        ≤ (q : ℚ) / 2 + 1 + ((q : ℚ) - 1) / 2 * (m : ℚ) :=
    add_le_add hd_le hcm_le
  have hcore_le :
      core ≤ (q : ℚ) / 3 * (m : ℚ) + (q : ℚ) / 2 + 1
                + ((q : ℚ) - 1) / 2 * (m : ℚ) := by
    simpa [core, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using (add_le_add hℓm_le h_d_add_c)
  let B2 : ℚ :=
    (q : ℚ) / 3 * (m : ℚ) + (q : ℚ) / 2 + 1
      + ((q : ℚ) - 1) / 2 * (m : ℚ)
  have hcore_le_B2 : core ≤ B2 := by
    simpa [B2, add_comm, add_left_comm, add_assoc] using hcore_le
  have h_num_pos :
      0 < (q : ℚ) * ((m : ℚ) - 3) + 3 * ((m : ℚ) - 2) := by
    refine add_pos_of_nonneg_of_pos ?_ ?_
    · exact mul_nonneg (le_of_lt hq_pos) (sub_nonneg.mpr (by exact_mod_cast hm3'))
    · have hm_gt2_nat : 2 < m := lt_of_lt_of_le (by decide : 2 < 3) hm3'
      exact mul_pos (by norm_num) (sub_pos.mpr (by exact_mod_cast hm_gt2_nat))
  have h_eq :
      6 * ((m : ℚ) * (q : ℚ) - B2)
        = (q : ℚ) * ((m : ℚ) - 3) + 3 * ((m : ℚ) - 2) := by
    simpa [B2] using (by ring :
      6 * ((m : ℚ) * (q : ℚ) -
            ((q : ℚ) / 3 * (m : ℚ) + (q : ℚ) / 2 + 1
              + ((q : ℚ) - 1) / 2 * (m : ℚ)))
        = (q : ℚ) * ((m : ℚ) - 3) + 3 * ((m : ℚ) - 2))
  have h6Δ_pos : 0 < 6 * ((m : ℚ) * (q : ℚ) - B2) := by
    simpa [h_eq] using h_num_pos
  have hΔ_pos : 0 < (m : ℚ) * (q : ℚ) - B2 := by
    have h6Δ_pos' : 0 < ((m : ℚ) * (q : ℚ) - B2) * 6 := by
      simpa [mul_comm] using h6Δ_pos
    exact pos_of_mul_pos_left h6Δ_pos' (by norm_num)
  have hB2_lt : B2 < (m : ℚ) * (q : ℚ) := sub_pos.mp hΔ_pos
  have hcore_lt_mq : core < (m : ℚ) * (q : ℚ) :=
    lt_of_le_of_lt hcore_le_B2 hB2_lt
  have hcore_lt_mq_addJm1 :
      core + (Jm1 : ℚ) * (q : ℚ)
        < (m : ℚ) * (q : ℚ) + (Jm1 : ℚ) * (q : ℚ) :=
    add_lt_add_left hcore_lt_mq _
  have hdeg_lt_mqJm1_rat :
      (R.natDegree : ℚ) < (m : ℚ) * (q : ℚ) + (Jm1 : ℚ) * (q : ℚ) :=
    lt_of_le_of_lt hdeg_core_le hcore_lt_mq_addJm1
  have hJreal_nonneg : (0 : ℚ) ≤ Jreal := by
    have h1 : (0 : ℚ) ≤ (ℓ : ℚ) / 2 :=
      div_nonneg (by exact_mod_cast (Nat.zero_le ℓ)) (by norm_num)
    have hnum : (0 : ℚ) ≤ (ℓ : ℚ) ^ 2 * (m : ℚ) := by
      have hℓsq_nonneg : (0 : ℚ) ≤ (ℓ : ℚ) ^ 2 := by
        simp
      exact mul_nonneg hℓsq_nonneg (by exact_mod_cast (Nat.zero_le m))
    have h2 : (0 : ℚ) ≤ (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ) :=
      div_nonneg hnum (le_of_lt hq_pos)
    have := add_nonneg h1 h2
    simpa [Jreal, hJreal_def] using this
  have hJm1_le_Jreal : (Jm1 : ℚ) ≤ Jreal := by
    have hceil_sub : (Nat.ceil Jreal : ℚ) - 1 ≤ Jreal := by
      have h1 : (Nat.ceil Jreal : ℚ) ≤ Jreal + 1 :=
        le_of_lt (Nat.ceil_lt_add_one hJreal_nonneg)
      linarith
    have hJ_eq : J = Nat.ceil Jreal := by simp [hJ_def]
    have hJ_ge_one : 1 ≤ J := by
      simpa [Jreal, hJreal_def, hJ_def] using hJ_pos
    have hJm1_cast : (Jm1 : ℚ) = (J : ℚ) - 1 := by
      simpa [Jm1] using (Nat.cast_sub (R := ℚ) hJ_ge_one)
    simpa [hJ_def, hJm1_cast] using hceil_sub
  have hJm1q_le : (Jm1 : ℚ) * (q : ℚ) ≤ Jreal * (q : ℚ) := by
    exact mul_le_mul_of_nonneg_right hJm1_le_Jreal (le_of_lt hq_pos)
  have hJrealq_eq :
      Jreal * (q : ℚ) =
        (ℓ : ℚ) * (q : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) := by
    simp [Jreal, div_eq_mul_inv, mul_add,
      mul_comm, mul_assoc, (ne_of_gt hq_pos)]
  have hJm1q_le_target :
      (Jm1 : ℚ) * (q : ℚ)
        ≤ (ℓ : ℚ) * (q : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) := by
    simpa [hJrealq_eq] using hJm1q_le
  have h_total_le :
      (m : ℚ) * (q : ℚ) + (Jm1 : ℚ) * (q : ℚ)
        ≤ (m : ℚ) * (q : ℚ)
          + (ℓ : ℚ) * (q : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) := by
    simpa [add_assoc] using
      (add_le_add_right hJm1q_le_target ((m : ℚ) * (q : ℚ)))
  have hdeg_lt_target_Q :
      (R.natDegree : ℚ)
        < (m : ℚ) * (q : ℚ)
          + (ℓ : ℚ) * (q : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) :=
    lt_of_lt_of_le hdeg_lt_mqJm1_rat h_total_le
  have hdeg_lt_target_R :
      (R.natDegree : ℝ)
        < ((m * q : ℕ) : ℝ)
          + ((ℓ * q : ℕ) : ℝ) / 2
          + ((ℓ ^ 2 * m : ℕ) : ℝ) := by
    have h' :
        (R.natDegree : ℝ) <
          ((m : ℚ) * (q : ℚ)
            + (ℓ : ℚ) * (q : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) : ℝ) := by
      exact_mod_cast hdeg_lt_target_Q
    simpa [Nat.cast_mul, pow_two, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc] using h'
  refine ⟨R, hR_ne_zero, ?_, ?_⟩
  · simpa [hm_def, pow_two, Nat.mul_assoc] using hdeg_lt_target_R
  · intro x hx k hk
    rcases hx with hx_zero | hx_pow
    · simpa using
        (stepanov_vanishing_roots
          (F := F) (f := f)
          (g :=
            Finset.sum (Finset.range J)
              (fun j =>
                ((rj j) + (sj j) * f ^ c) * Polynomial.X ^ (j * q)))
          (ℓ := ℓ) (x := x) hx_zero k hk)
    · by_cases hx0 : f.eval x = 0
      · simpa using
          (stepanov_vanishing_roots
            (F := F) (f := f)
            (g :=
              Finset.sum (Finset.range J)
                (fun j =>
                  ((rj j) + (sj j) * f ^ c) * Polynomial.X ^ (j * q)))
            (ℓ := ℓ) (x := x) hx0 k hk)
      · have hvan_x :
            ∀ k' < ℓ,
              Finset.sum (Finset.range J)
                (fun j =>
                  (((hasseDerivOp F k' (f ^ ℓ * rj j)) /
                        f ^ (ℓ - k')).eval x
                      +
                      a *
                        ((hasseDerivOp F k' (f ^ (ℓ + c) * sj j)) /
                            f ^ (ℓ + c - k')).eval x) *
                    x ^ j) = 0 :=
          hvan x hx0 hx_pow
        have h_all_k :=
          stepanov_vanishing_nonzeros
            (F := F) (f := f) (ℓ := ℓ) (q := q)
            (c := c) (J := J) hq rj sj a x
            (fun k' hk' => lt_of_lt_of_le hk' (le_trans hl (Nat.div_le_self _ _)))
            hvan_x hx0 hx_pow
        exact h_all_k k hk
