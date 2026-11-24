-- Prove2me | solution 1 for riemann_hypothesis_stepanov_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T18:38:42.103544+00:00
-- url     : https://prove2.me/submissions/cd56c09c-afb8-444e-870c-b705457da83c

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
import Theorems.Thm_hasse_vanishing_card_bound
import Theorems.Thm_stepanov_polynomial

section






lemma ceil_sqrt_le_div_three
  (q : ℕ) (hq : 15 ≤ q) :
  Nat.ceil (Real.sqrt q) ≤ q / 3 :=
by
  set k : ℕ := q / 3 with hk
  have hk_ge5 : 5 ≤ k := by
    have : 5 * 3 ≤ q := by simpa using hq
    simpa [hk] using (Nat.le_div_iff_mul_le (by decide : 0 < 3)).2 this
  have hq_le_2plus3k : q ≤ 2 + 3 * k := by
    have hmod : q % 3 ≤ 2 :=
      Nat.lt_succ_iff.mp (Nat.mod_lt q (by decide : 0 < 3))
    have h : q % 3 + k * 3 ≤ 2 + k * 3 := Nat.add_le_add_right hmod _
    simpa [hk, Nat.mod_add_div, Nat.mul_comm] using h
  have h2plus3k_le_kk : 2 + 3 * k ≤ k * k := by
    have h2_le_k : 2 ≤ k := (by decide : 2 ≤ 5).trans hk_ge5
    have h4_le_k : 4 ≤ k := (by decide : 4 ≤ 5).trans hk_ge5
    calc
      2 + 3 * k ≤ k + 3 * k := Nat.add_le_add_right h2_le_k _
      _ = 4 * k := by ring_nf
      _ ≤ k * k := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left k h4_le_k
  have h_sqrt_le : Real.sqrt (q : ℝ) ≤ k := by
    refine (Real.sqrt_le_iff).2 ?_
    refine ⟨?_, ?_⟩
    · exact_mod_cast (Nat.zero_le k)
    · have : (q : ℝ) ≤ (k : ℝ) * k := by
        exact_mod_cast (hq_le_2plus3k.trans h2plus3k_le_kk)
      simpa [pow_two] using this
  have : Nat.ceil (Real.sqrt (q : ℝ)) ≤ k := Nat.ceil_le.2 h_sqrt_le
  simpa [hk] using this















end



theorem solution
  (F : Type*) [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
  (f : Polynomial F) (q : ℕ) (a : F)
  (hq : q = Fintype.card F)
  (hm3 : 3 ≤ f.natDegree)
  (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
      g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
  (hq6m : q > 6 * f.natDegree)
  [DecidablePred (fun x : F => x ∈ S_a F f ((q - 1) / 2) a)] :
  (Fintype.card {x : F // x ∈ S_a F f ((q - 1) / 2) a} : ℝ)
    < (q : ℝ) / 2 + 2 * (f.natDegree : ℝ) * (Nat.ceil (Real.sqrt q) : ℝ) :=
by
  set m : ℕ := f.natDegree with hm_def
  have h18_lt_q : 18 < q := by
    have : 18 ≤ 6 * m := by
      have : 3 ≤ m := by simpa [hm_def] using hm3
      have := Nat.mul_le_mul_left 6 this
      simpa using this
    exact lt_of_le_of_lt this (by simpa [hm_def] using hq6m)
  have h15_le_q : (15 : ℕ) ≤ q :=
    le_trans (by decide : (15 : ℕ) ≤ 19) (Nat.succ_le_of_lt h18_lt_q)
  have hq_pos_nat : 0 < q := lt_trans (by decide : 0 < 18) h18_lt_q
  set ℓ : ℕ := Nat.ceil (Real.sqrt q) with hℓ_def
  have hℓ_le_q_div3 : ℓ ≤ q / 3 := by
    simpa [ℓ, hℓ_def] using ceil_sqrt_le_div_three q h15_le_q
  have h_sqrt_le_ℓ : Real.sqrt q ≤ (ℓ : ℝ) := by
    have hceil : Real.sqrt q ≤ (Nat.ceil (Real.sqrt q) : ℝ) :=
      Nat.le_ceil (Real.sqrt q)
    simpa [ℓ, hℓ_def] using hceil
  have hℓ_pos_real : 0 < (ℓ : ℝ) :=
    lt_of_lt_of_le (Real.sqrt_pos.mpr (by exact_mod_cast hq_pos_nat)) h_sqrt_le_ℓ
  have hℓ_pos : 0 < ℓ := by exact_mod_cast hℓ_pos_real
  obtain ⟨R, hR_ne, hdegR, hvan⟩ :=
    stepanov_polynomial (F := F) (hF := hF) (f := f) (q := q) (ℓ := ℓ) (a := a)
      hq hm3 hnsq hq6m hℓ_pos hℓ_le_q_div3
  set Sfin : Finset F :=
    Finset.univ.filter (fun x : F => x ∈ S_a F f ((q - 1) / 2) a) with hSfin_def
  have hvan_S : ∀ x ∈ Sfin, ∀ k < ℓ, (hasseDerivOp F k R).eval x = 0 := by
    intro x hx k hk
    rcases Finset.mem_filter.mp hx with ⟨_, hx_sa⟩
    exact hvan x hx_sa k hk
  have h_card_Sfin_le :
      (Sfin.card : ℝ) ≤ (R.natDegree : ℝ) / (ℓ : ℝ) :=
    hasse_vanishing_card_bound (F := F) (r := R) (ℓ := ℓ) (S := Sfin)
      hR_ne hℓ_pos hvan_S
  have h_card_subtype_eq :
      (Fintype.card {x : F // x ∈ S_a F f ((q - 1) / 2) a} : ℝ)
        = (Sfin.card : ℝ) := by
    exact_mod_cast (by
      simp [Sfin] :
        Fintype.card {x : F // x ∈ S_a F f ((q - 1) / 2) a} = Sfin.card)
  have h_card_le :
      (Fintype.card {x : F // x ∈ S_a F f ((q - 1) / 2) a} : ℝ)
        ≤ (R.natDegree : ℝ) / (ℓ : ℝ) := by
    simpa [h_card_subtype_eq] using h_card_Sfin_le
  have hdegR' :
      (R.natDegree : ℝ)
        < (m : ℝ) * (q : ℝ)
          + (ℓ : ℝ) * (q : ℝ) / 2
          + (ℓ : ℝ) ^ 2 * (m : ℝ) := by
    have hfdeg : f.natDegree = m := by simp [hm_def]
    have h1 : ((f.natDegree * q : ℕ) : ℝ) = (m : ℝ) * (q : ℝ) := by
      simp [hfdeg, Nat.cast_mul, mul_comm]
    have h2 : ((ℓ * q : ℕ) : ℝ) = (ℓ : ℝ) * (q : ℝ) := by
      simp [Nat.cast_mul, mul_comm]
    have h3 : ((ℓ * ℓ * f.natDegree : ℕ) : ℝ)
        = (ℓ : ℝ) ^ 2 * (m : ℝ) := by
      simp [hfdeg, Nat.cast_mul, pow_two, mul_comm]
    simpa [h1, h2, h3] using hdegR
  have hq_le_ℓsq : (q : ℝ) ≤ (ℓ : ℝ) ^ 2 := by
    have h_sq_le :
        Real.sqrt q * Real.sqrt q ≤ (ℓ : ℝ) * (ℓ : ℝ) :=
      mul_self_le_mul_self (a := Real.sqrt q) (b := (ℓ : ℝ))
        (Real.sqrt_nonneg _) h_sqrt_le_ℓ
    have hsq_eq : Real.sqrt q * Real.sqrt q = (q : ℝ) := by simp
    simpa [hsq_eq, pow_two] using h_sq_le
  have h_mq_le_mℓsq :
      (m : ℝ) * (q : ℝ)
        ≤ (m : ℝ) * (ℓ : ℝ) ^ 2 := by
    have :=
      mul_le_mul_of_nonneg_left hq_le_ℓsq
        (by exact_mod_cast (Nat.zero_le m) : 0 ≤ (m : ℝ))
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hdegR_upper :
      (R.natDegree : ℝ)
        < (ℓ : ℝ) * (q : ℝ) / 2 + 2 * (m : ℝ) * (ℓ : ℝ) ^ 2 := by
    have h1 :
        (m : ℝ) * (q : ℝ) + (ℓ : ℝ) ^ 2 * (m : ℝ)
          ≤ (m : ℝ) * (ℓ : ℝ) ^ 2 + (ℓ : ℝ) ^ 2 * (m : ℝ) :=
      add_le_add_left h_mq_le_mℓsq _
    have h2 :
        (m : ℝ) * (ℓ : ℝ) ^ 2 + (ℓ : ℝ) ^ 2 * (m : ℝ)
          = 2 * (m : ℝ) * (ℓ : ℝ) ^ 2 := by
      calc
        (m : ℝ) * (ℓ : ℝ) ^ 2 + (ℓ : ℝ) ^ 2 * (m : ℝ)
            = (m : ℝ) * (ℓ : ℝ) ^ 2 + (m : ℝ) * (ℓ : ℝ) ^ 2 := by
              simp [mul_comm]
        _ = 2 * (m : ℝ) * (ℓ : ℝ) ^ 2 := by ring
    have h3 :
        (m : ℝ) * (q : ℝ) + (ℓ : ℝ) ^ 2 * (m : ℝ)
          ≤ 2 * (m : ℝ) * (ℓ : ℝ) ^ 2 := by
      simpa [h2] using h1
    have h4 :
        (m : ℝ) * (q : ℝ) + (ℓ : ℝ) * (q : ℝ) / 2
          + (ℓ : ℝ) ^ 2 * (m : ℝ)
          ≤ (ℓ : ℝ) * (q : ℝ) / 2
            + 2 * (m : ℝ) * (ℓ : ℝ) ^ 2 := by
      have := add_le_add_left h3 ((ℓ : ℝ) * (q : ℝ) / 2)
      simpa [add_comm, add_left_comm, add_assoc] using this
    exact lt_of_lt_of_le hdegR' h4
  have hdeg_div_main :
      (R.natDegree : ℝ) / (ℓ : ℝ)
        < (q : ℝ) / 2 + 2 * (m : ℝ) * (ℓ : ℝ) := by
    have hdeg_div :
        (R.natDegree : ℝ) / (ℓ : ℝ)
          < ((ℓ : ℝ) * (q : ℝ) / 2
              + 2 * (m : ℝ) * (ℓ : ℝ) ^ 2) / (ℓ : ℝ) := by
      have := mul_lt_mul_of_pos_right hdegR_upper (inv_pos.mpr hℓ_pos_real)
      simpa [div_eq_mul_inv] using this
    have h_upper_simpl :
        ((ℓ : ℝ) * (q : ℝ) / 2 + 2 * (m : ℝ) * (ℓ : ℝ) ^ 2) / (ℓ : ℝ)
          = (q : ℝ) / 2 + 2 * (m : ℝ) * (ℓ : ℝ) := by
      have hneq : (ℓ : ℝ) ≠ 0 := ne_of_gt hℓ_pos_real
      calc
        ((ℓ : ℝ) * (q : ℝ) / 2 + 2 * (m : ℝ) * (ℓ : ℝ) ^ 2) / (ℓ : ℝ)
            = (ℓ : ℝ) * (q : ℝ) / 2 / (ℓ : ℝ)
                + (2 * (m : ℝ) * (ℓ : ℝ) ^ 2) / (ℓ : ℝ) := by
                  field_simp [add_comm, add_left_comm, add_assoc]
        _ = (q : ℝ) / 2 + 2 * (m : ℝ) * (ℓ : ℝ) := by
          have h1 : (ℓ : ℝ) * (q : ℝ) / 2 / (ℓ : ℝ) = (q : ℝ) / 2 := by
            field_simp [hneq, mul_comm, mul_left_comm, mul_assoc]
          have h2 : (2 * (m : ℝ) * (ℓ : ℝ) ^ 2) / (ℓ : ℝ)
              = 2 * (m : ℝ) * (ℓ : ℝ) := by
            field_simp [hneq, pow_two, mul_comm, mul_left_comm, mul_assoc]
          simp [h1, h2]
    simpa [h_upper_simpl] using hdeg_div
  have :
      (Fintype.card {x : F // x ∈ S_a F f ((q - 1) / 2) a} : ℝ)
        < (q : ℝ) / 2 + 2 * (m : ℝ) * (ℓ : ℝ) :=
    lt_of_le_of_lt h_card_le hdeg_div_main
  simpa [m, hm_def, ℓ, hℓ_def] using this
