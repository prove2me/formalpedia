-- Prove2me | solution 1 for mme_stothers_fixed_profile_rate_below_marginal_multinomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:09:34.281781+00:00
-- url     : https://prove2.me/submissions/09a049d6-6eb4-45d3-8e78-a11acc34358f

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Definitions.Def_mme_stothers_fixed_outer_profile
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower

open MME BigOperators Filter Topology

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000

namespace MME.StothersFourth

private theorem exp_log_two_entropyBits_eq_prod_rpow
    {D : Type*} [Fintype D]
    (p : D → ℝ) (hp : ∀ i, 0 < p i) :
    Real.exp (Real.log 2 * mme_modern_entropyBits p) =
      ∏ i, Real.rpow (p i) (-p i) := by
  have hlog2 : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  rw [show Real.log 2 * mme_modern_entropyBits p =
      ∑ i, -(p i * Real.log (p i)) by
    unfold mme_modern_entropyBits
    rw [mul_div_cancel₀ _ hlog2]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Real.negMulLog_def]
    ring]
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [show Real.rpow (p i) (-p i) =
      Real.exp (Real.log (p i) * (-p i)) from
    Real.rpow_def_of_pos (hp i) (-p i)]
  congr 1
  ring

private noncomputable def fixedMarginalProfile (j : Fin 9) : ℝ :=
  (fixedMarginalBaseCount j : ℝ) / (3 * fixedProfileScale : ℕ)

private noncomputable def fixedMarginalRate : ℝ :=
  ∏ j : Fin 9,
    Real.rpow (fixedMarginalProfile j) (-fixedMarginalProfile j)

private noncomputable def fixedCapacityInner (tau : ℝ) (m : ℕ) : ℝ :=
  ∏ r : Fin 10,
    (classValue 6 tau r) ^
      (classMultiplicity r * fixedProfileCount m r)

private theorem fixedProfileB_pos (i : Fin 10) :
    0 < fixedProfileB i := by
  fin_cases i <;>
    norm_num [fixedProfileB, fixedProfileBaseCount, fixedProfileScale]

private theorem fixedProfileB_explicit :
    fixedProfileB =
      ![(98 : ℝ) / 97942072,
        (1862 : ℝ) / 97942072,
        (73075 : ℝ) / 97942072,
        (1023050 : ℝ) / 97942072,
        (3626000 : ℝ) / 97942072,
        (98000 : ℝ) / 97942072,
        (2156000 : ℝ) / 97942072,
        (13720000 : ℝ) / 97942072,
        (21560000 : ℝ) / 97942072,
        (38710000 : ℝ) / 97942072] := by
  funext i
  fin_cases i <;>
    norm_num [fixedProfileB, fixedProfileBaseCount, fixedProfileScale]

private theorem fixedClassValue_pos (tau : ℝ) (i : Fin 10) :
    0 < classValue 6 tau i := by
  fin_cases i <;>
    simp [classValue, E, H, L] <;> positivity

private theorem fixedMarginalProfile_pos (j : Fin 9) :
    0 < fixedMarginalProfile j := by
  fin_cases j <;>
    norm_num [fixedMarginalProfile, fixedMarginalBaseCount,
      fixedProfileScale]

private theorem marginal_fixedProfileB_eq (j : Fin 9) :
    marginal fixedProfileB j = fixedMarginalProfile j := by
  rw [fixedProfileB_explicit]
  fin_cases j <;>
    simp [marginal, Q,
      fixedMarginalProfile, fixedMarginalBaseCount, fixedProfileScale]
      <;> norm_num

private theorem fixed_profile_exponent_identity
    (m : ℕ) (i : Fin 10) :
    (fixedProfileB i / 3) *
        (((classMultiplicity i * fixedOuterLength m : ℕ) : ℝ)) =
      ((classMultiplicity i * fixedProfileCount m i : ℕ) : ℝ) := by
  unfold fixedProfileB fixedProfileCount fixedOuterLength
  push_cast
  norm_num [fixedProfileScale]
  ring

private theorem fixed_globalRate_pow_factorization
    (tau : ℝ) (m : ℕ) :
    (globalRate 6 tau fixedProfileB fixedProfileB) ^
        (fixedOuterLength m) =
      fixedCapacityInner tau m *
        fixedMarginalRate ^ (fixedOuterLength m) := by
  have hcancel (i : Fin 10) :
      Real.rpow (fixedProfileB i) (fixedProfileB i) *
          Real.rpow (fixedProfileB i) (-fixedProfileB i) = 1 := by
    change fixedProfileB i ^ fixedProfileB i *
      fixedProfileB i ^ (-fixedProfileB i) = 1
    rw [← Real.rpow_add (fixedProfileB_pos i)]
    simp
  have houter :
      (∏ i : Fin 10,
        (Real.rpow (classValue 6 tau i) (fixedProfileB i / 3) *
          Real.rpow (fixedProfileB i) (fixedProfileB i) *
          Real.rpow (fixedProfileB i) (-fixedProfileB i)) ^
            classMultiplicity i) =
        ∏ i : Fin 10,
          (Real.rpow (classValue 6 tau i) (fixedProfileB i / 3)) ^
            classMultiplicity i := by
    apply Finset.prod_congr rfl
    intro i _hi
    rw [mul_assoc, hcancel, mul_one]
  rw [globalRate, houter]
  rw [mul_pow]
  congr 1
  · rw [← Finset.prod_pow]
    unfold fixedCapacityInner
    apply Finset.prod_congr rfl
    intro i _hi
    rw [← pow_mul]
    calc
      (Real.rpow (classValue 6 tau i) (fixedProfileB i / 3)) ^
            (classMultiplicity i * fixedOuterLength m) =
          Real.rpow (classValue 6 tau i)
            ((fixedProfileB i / 3) *
              ((classMultiplicity i * fixedOuterLength m : ℕ) : ℝ)) := by
        exact (Real.rpow_mul_natCast
          (fixedClassValue_pos tau i).le
          (fixedProfileB i / 3)
          (classMultiplicity i * fixedOuterLength m)).symm
      _ = Real.rpow (classValue 6 tau i)
          ((classMultiplicity i * fixedProfileCount m i : ℕ) : ℝ) := by
        rw [fixed_profile_exponent_identity]
      _ = (classValue 6 tau i) ^
          (classMultiplicity i * fixedProfileCount m i) :=
        Real.rpow_natCast _ _
  · unfold fixedMarginalRate
    apply congrArg (fun x : ℝ ↦ x ^ fixedOuterLength m)
    apply Finset.prod_congr rfl
    intro j _hj
    rw [marginal_fixedProfileB_eq]

private theorem fixedMarginalBaseCount_sum :
    ∑ j : Fin 9, fixedMarginalBaseCount j = 3 * fixedProfileScale := by
  norm_num [fixedMarginalBaseCount, fixedProfileScale, Fin.sum_univ_succ]

private theorem fixed_marginal_multinomial_entropy_bound
    (m : ℕ) (hm : 0 < m) :
    fixedMarginalRate ^ (fixedOuterLength m) ≤
      (6 * (((fixedOuterLength m + 1 : ℕ) : ℝ))) ^ 9 *
        (Nat.multinomial Finset.univ
          (fun j : Fin 9 ↦ fixedMarginalBaseCount j * m) : ℝ) := by
  have hsumPos : 0 < ∑ j : Fin 9, fixedMarginalBaseCount j := by
    rw [fixedMarginalBaseCount_sum]
    norm_num [fixedProfileScale]
  have hlower := mme_dwz_multinomial_entropy_polynomial_lower
    fixedMarginalBaseCount m hm hsumPos
  have hprofile :
      (fun j ↦ (fixedMarginalBaseCount j : ℝ) /
        (((∑ k : Fin 9, fixedMarginalBaseCount k : ℕ) : ℝ))) =
        fixedMarginalProfile := by
    funext j
    rw [fixedMarginalBaseCount_sum]
    rfl
  rw [hprofile, fixedMarginalBaseCount_sum] at hlower
  have hentropy :=
    exp_log_two_entropyBits_eq_prod_rpow
      fixedMarginalProfile fixedMarginalProfile_pos
  have hNcast :
      ((fixedOuterLength m : ℕ) : ℝ) =
        (m : ℝ) * ((3 * fixedProfileScale : ℕ) : ℝ) := by
    unfold fixedOuterLength
    push_cast
    ring
  have hlhs :
      Real.exp
          ((m : ℝ) * (((3 * fixedProfileScale : ℕ) : ℝ) *
            Real.log 2 * mme_modern_entropyBits fixedMarginalProfile)) =
        fixedMarginalRate ^ fixedOuterLength m := by
    rw [show
        (m : ℝ) * (((3 * fixedProfileScale : ℕ) : ℝ) *
            Real.log 2 * mme_modern_entropyBits fixedMarginalProfile) =
          ((fixedOuterLength m : ℕ) : ℝ) *
            (Real.log 2 * mme_modern_entropyBits fixedMarginalProfile) by
      rw [hNcast]
      ring]
    rw [Real.exp_nat_mul]
    rw [hentropy]
    rfl
  rw [hlhs] at hlower
  simpa only [Fintype.card_fin, fixedOuterLength, mul_assoc] using hlower

private noncomputable def fixedPolyC : ℝ :=
  (6 : ℝ) ^ 9 * (Nat.factorial 18 : ℝ) + 1

private theorem fixed_polynomial_le_exp_sqrt (m : ℕ) :
    (6 * (((fixedOuterLength m + 1 : ℕ) : ℝ))) ^ 9 ≤
      Real.exp
        (fixedPolyC * Real.sqrt
          (((fixedOuterLength m + 1 : ℕ) : ℝ))) := by
  let x : ℝ := Real.sqrt
    (((fixedOuterLength m + 1 : ℕ) : ℝ))
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x ^ 2 = (((fixedOuterLength m + 1 : ℕ) : ℝ)) := by
    dsimp only [x]
    exact Real.sq_sqrt (by positivity)
  have hx1 : 1 ≤ x := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    norm_num
  have h18 := Real.pow_div_factorial_le_exp x hx0 18
  have hpoly :
      (6 * (((fixedOuterLength m + 1 : ℕ) : ℝ))) ^ 9 ≤
        (6 : ℝ) ^ 9 * (Nat.factorial 18 : ℝ) * Real.exp x := by
    have hx18 : x ^ 18 ≤ (Nat.factorial 18 : ℝ) * Real.exp x := by
      have hfac : 0 < (Nat.factorial 18 : ℝ) := by positivity
      simpa [mul_comm] using (div_le_iff₀ hfac).mp h18
    calc
      (6 * (((fixedOuterLength m + 1 : ℕ) : ℝ))) ^ 9 =
          (6 : ℝ) ^ 9 * x ^ 18 := by
        rw [← hx2, mul_pow, ← pow_mul]
      _ ≤ (6 : ℝ) ^ 9 *
          ((Nat.factorial 18 : ℝ) * Real.exp x) :=
        mul_le_mul_of_nonneg_left hx18 (by positivity)
      _ = (6 : ℝ) ^ 9 * (Nat.factorial 18 : ℝ) * Real.exp x := by
        ring
  have hconst :
      (6 : ℝ) ^ 9 * (Nat.factorial 18 : ℝ) ≤
        Real.exp ((fixedPolyC - 1) * x) := by
    have hExpLower := Real.add_one_le_exp ((fixedPolyC - 1) * x)
    have hxlarge :
        (6 : ℝ) ^ 9 * (Nat.factorial 18 : ℝ) ≤
          1 + (fixedPolyC - 1) * x := by
      have hc : fixedPolyC - 1 =
          (6 : ℝ) ^ 9 * (Nat.factorial 18 : ℝ) := by
        unfold fixedPolyC
        ring
      rw [hc]
      nlinarith [mul_le_mul_of_nonneg_left hx1
        (by positivity : 0 ≤ (6 : ℝ) ^ 9 * (Nat.factorial 18 : ℝ))]
    exact hxlarge.trans (by simpa [add_comm] using hExpLower)
  calc
    (6 * (((fixedOuterLength m + 1 : ℕ) : ℝ))) ^ 9 ≤
        (6 : ℝ) ^ 9 * (Nat.factorial 18 : ℝ) * Real.exp x := hpoly
    _ ≤ Real.exp ((fixedPolyC - 1) * x) * Real.exp x := by gcongr
    _ = Real.exp (fixedPolyC * x) := by
      rw [← Real.exp_add]
      congr 1
      ring

private theorem fixed_profile_rate_below_marginal_multinomial
    (tau : ℝ) :
    ∀ᶠ m : ℕ in atTop,
      (globalRate 6 tau fixedProfileB fixedProfileB) ^
            (fixedOuterLength m) *
          Real.exp
            (-fixedPolyC * Real.sqrt
              (((fixedOuterLength m + 1 : ℕ) : ℝ))) ≤
        (Nat.multinomial Finset.univ
            (fun j : Fin 9 ↦ fixedMarginalBaseCount j * m) : ℝ) *
          fixedCapacityInner tau m := by
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hmulti := fixed_marginal_multinomial_entropy_bound m hm
  have hpoly := fixed_polynomial_le_exp_sqrt m
  have hinner : 0 ≤ fixedCapacityInner tau m := by
    unfold fixedCapacityInner
    exact Finset.prod_nonneg fun i _ ↦
      pow_nonneg (fixedClassValue_pos tau i).le _
  have hmarg : 0 ≤ fixedMarginalRate ^ fixedOuterLength m := by
    exact pow_nonneg (Finset.prod_nonneg fun j _ ↦
      (Real.rpow_pos_of_pos (fixedMarginalProfile_pos j) _).le) _
  have hexpPos : 0 < Real.exp
      (fixedPolyC * Real.sqrt
        (((fixedOuterLength m + 1 : ℕ) : ℝ))) := Real.exp_pos _
  have hmargScaled :
      fixedMarginalRate ^ fixedOuterLength m *
          Real.exp
            (-fixedPolyC * Real.sqrt
              (((fixedOuterLength m + 1 : ℕ) : ℝ))) ≤
        (Nat.multinomial Finset.univ
          (fun j : Fin 9 ↦ fixedMarginalBaseCount j * m) : ℝ) := by
    calc
      fixedMarginalRate ^ fixedOuterLength m *
          Real.exp
            (-fixedPolyC * Real.sqrt
              (((fixedOuterLength m + 1 : ℕ) : ℝ))) ≤
          ((6 * (((fixedOuterLength m + 1 : ℕ) : ℝ))) ^ 9 *
            (Nat.multinomial Finset.univ
              (fun j : Fin 9 ↦ fixedMarginalBaseCount j * m) : ℝ)) *
            Real.exp
              (-fixedPolyC * Real.sqrt
                (((fixedOuterLength m + 1 : ℕ) : ℝ))) := by
            gcongr
      _ ≤
          (Real.exp
              (fixedPolyC * Real.sqrt
                (((fixedOuterLength m + 1 : ℕ) : ℝ))) *
            (Nat.multinomial Finset.univ
              (fun j : Fin 9 ↦ fixedMarginalBaseCount j * m) : ℝ)) *
            Real.exp
              (-fixedPolyC * Real.sqrt
                (((fixedOuterLength m + 1 : ℕ) : ℝ))) := by
            gcongr
      _ = (Nat.multinomial Finset.univ
          (fun j : Fin 9 ↦ fixedMarginalBaseCount j * m) : ℝ) := by
        calc
          Real.exp
                (fixedPolyC * Real.sqrt
                  (((fixedOuterLength m + 1 : ℕ) : ℝ))) *
              (Nat.multinomial Finset.univ
                (fun j : Fin 9 ↦ fixedMarginalBaseCount j * m) : ℝ) *
              Real.exp
                (-fixedPolyC * Real.sqrt
                  (((fixedOuterLength m + 1 : ℕ) : ℝ))) =
            (Nat.multinomial Finset.univ
                (fun j : Fin 9 ↦ fixedMarginalBaseCount j * m) : ℝ) *
              (Real.exp
                  (fixedPolyC * Real.sqrt
                    (((fixedOuterLength m + 1 : ℕ) : ℝ))) *
                Real.exp
                  (-fixedPolyC * Real.sqrt
                    (((fixedOuterLength m + 1 : ℕ) : ℝ)))) := by ring
          _ = (Nat.multinomial Finset.univ
              (fun j : Fin 9 ↦ fixedMarginalBaseCount j * m) : ℝ) := by
            rw [← Real.exp_add]
            simp
  rw [fixed_globalRate_pow_factorization]
  calc
    (fixedCapacityInner tau m *
          fixedMarginalRate ^ fixedOuterLength m) *
        Real.exp
          (-fixedPolyC * Real.sqrt
            (((fixedOuterLength m + 1 : ℕ) : ℝ))) =
      fixedCapacityInner tau m *
        (fixedMarginalRate ^ fixedOuterLength m *
          Real.exp
            (-fixedPolyC * Real.sqrt
              (((fixedOuterLength m + 1 : ℕ) : ℝ)))) := by ring
    _ ≤ fixedCapacityInner tau m *
        (Nat.multinomial Finset.univ
          (fun j : Fin 9 ↦ fixedMarginalBaseCount j * m) : ℝ) := by
      gcongr
    _ = (Nat.multinomial Finset.univ
          (fun j : Fin 9 ↦ fixedMarginalBaseCount j * m) : ℝ) *
        fixedCapacityInner tau m := by ring

/-- The marginal multinomial supplies the entire scalar part of the fixed
Stothers global rate, up to one uniform square-root-exponential loss.  The
constant is existential because its magnitude is irrelevant to the laser
limit; the proof above gives a completely explicit witness. -/
theorem mme_stothers_fixed_profile_rate_below_marginal_multinomial
    (tau : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        (globalRate 6 tau fixedProfileB fixedProfileB) ^
              (fixedOuterLength m) *
            Real.exp
              (-C * Real.sqrt
                (((fixedOuterLength m + 1 : ℕ) : ℝ))) ≤
          (Nat.multinomial Finset.univ
              (fun j : Fin 9 ↦ fixedMarginalBaseCount j * m) : ℝ) *
            (∏ r : Fin 10,
              (classValue 6 tau r) ^
                (classMultiplicity r * fixedProfileCount m r)) := by
  refine ⟨fixedPolyC, ?_, ?_⟩
  · unfold fixedPolyC
    positivity
  · simpa only [fixedCapacityInner] using
      fixed_profile_rate_below_marginal_multinomial tau

end MME.StothersFourth

theorem solution
    (tau : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in Filter.atTop,
        (MME.StothersFourth.globalRate 6 tau
              MME.StothersFourth.fixedProfileB
              MME.StothersFourth.fixedProfileB) ^
              (MME.StothersFourth.fixedOuterLength m) *
            Real.exp
              (-C * Real.sqrt
                (((MME.StothersFourth.fixedOuterLength m + 1 : ℕ) : ℝ))) ≤
          (Nat.multinomial Finset.univ
              (fun j : Fin 9 ↦
                MME.StothersFourth.fixedMarginalBaseCount j * m) : ℝ) *
            (∏ r : Fin 10,
              (MME.StothersFourth.classValue 6 tau r) ^
                (MME.StothersFourth.classMultiplicity r *
                  MME.StothersFourth.fixedProfileCount m r)) := by
  exact
    MME.StothersFourth.mme_stothers_fixed_profile_rate_below_marginal_multinomial
      tau
