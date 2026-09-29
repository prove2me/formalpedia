-- Prove2me | solution 1 for mme_dwz_q6_112_restricted_primary_certificates_to_six_symmetric_finite_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T14:06:48.877438+00:00
-- url     : https://prove2.me/submissions/8ab03602-0b82-47de-a218-667c426f3290

import Mathlib.Tactic
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_component_word_projection
import Theorems.Thm_mme_dwz_q6_112_table2_primary_hash_family_rate
import Theorems.Thm_mme_dwz_q6_112_fixed_profile_usable_rate_lower
import Theorems.Thm_mme_Ctensor_one_half_family_to_six_finite_rate_of_capacity

open Filter Topology
open MME MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedVariables false

private noncomputable def polyC112 : ℝ :=
  32 * 6 ^ 7 * ((14 : ℕ).factorial : ℝ)

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (hcertificate : ∀ (m A H : ℕ),
      CWQ6PrimaryHashFamily
          (50000000 * (20088623 * m))
          (21015 * (20088623 * m))
          (49978985 * (20088623 * m)) A H →
        Nonempty
          (CTensorOneHOneFamilyCertificate
            (restrictedComponentPower K (12 : Fin 15) m) A H
            (6 ^
              (4 * (49978985 * (20088623 * m)) +
                2 * (21015 * (20088623 * m)))))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∃ (q : ℕ) (A B Cdim : Fin q → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun j ↦ MMObj K (A j) (B j) (Cdim j)))
            (sixSymmetrization
              (restrictedComponentPower K (12 : Fin 15) m)) ∧
          (((componentBase tau (12 : Fin 15)) ^
              (MME.DWZTable2Counts.component (12 : Fin 15) * m)) ^ (6 : ℕ)) *
              Real.exp (-C * Real.sqrt
                (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
            ∑ j, (((A j * B j * Cdim j : ℕ) : ℝ) ^ tau) := by
  obtain ⟨C₀, hC₀, hfamilies⟩ :=
    mme_dwz_q6_112_table2_primary_hash_family_rate
  let Cprofile : ℝ := polyC112 + 5 * C₀
  let Cfinal : ℝ := 2 * Cprofile + 400
  have hpolyC : 0 ≤ polyC112 := by
    dsimp [polyC112]
    positivity
  have hCprofile : 0 ≤ Cprofile := by
    dsimp [Cprofile]
    positivity
  have hCfinal : 0 ≤ Cfinal := by
    dsimp [Cfinal]
    positivity
  refine ⟨Cfinal, hCfinal, ?_⟩
  have hscale :
      Tendsto (fun m : ℕ ↦ 20088623 * m) atTop atTop := by
    simpa [nsmul_eq_mul, mul_comm] using
      ((tendsto_id : Tendsto (fun x : ℕ ↦ x) atTop atTop).nsmul_atTop
        (by norm_num : 0 < (20088623 : ℕ)))
  have hpulled := hscale.eventually hfamilies
  filter_upwards [hpulled, eventually_gt_atTop 0]
    with m hfamily hm
  dsimp only at hfamily
  rcases hfamily with
    ⟨A, H, family, hHbound, hAlower, hHlower, hcapacity⟩
  let t : ℕ := 20088623 * m
  let N : ℕ := 50000000 * t
  let L : ℕ := 21015 * t
  let G : ℕ := 49978985 * t
  let Z : ℕ := Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
  let X : ℕ := Nat.choose N G
  let middle : ℕ := Nat.choose (2 * G) G
  let capacity : ℝ :=
    ((Z : ℝ) ^ 3 * (middle : ℝ) ^ 2) / (16 * (X : ℝ) ^ 4)
  let loss : ℝ :=
    Real.exp (-C₀ * Real.sqrt (((N + 1 : ℕ) : ℝ)))
  let volumeNat : ℕ := 6 ^ (4 * G + 2 * L)
  let volumeWeight : ℝ := (((volumeNat ^ 3 : ℕ) : ℝ) ^ tau)
  let R : ℝ := componentBase tau (12 : Fin 15) ^ 3
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hfamily' : CWQ6PrimaryHashFamily N L G A H := by
    simpa only [N, L, G, t] using family
  have hcapacity' :
      capacity * loss ^ 5 ≤
        (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) := by
    simpa only [N, L, G, Z, X, middle, capacity, loss,
      Nat.cast_pow] using hcapacity
  have hmiddleNat : 0 < middle := by
    dsimp [middle]
    exact Nat.choose_pos (by omega)
  have hmiddleReal : 0 < (middle : ℝ) := by
    exact_mod_cast hmiddleNat
  have hloss : 0 < loss := by
    dsimp [loss]
    positivity
  have hH : 0 < H := by
    by_contra hnot
    have hHzero : H = 0 := Nat.eq_zero_of_not_pos hnot
    subst H
    have hleft : 0 < (middle : ℝ) * loss :=
      mul_pos hmiddleReal hloss
    have hnonpos : (middle : ℝ) * loss ≤ 0 := by
      simpa only [N, L, G, X, middle, loss, Nat.cast_zero,
        zero_pow, mul_zero] using hHlower
    exact (not_lt_of_ge hnonpos) hleft
  obtain ⟨stars⟩ := hcertificate m A H (by
    simpa only [N, L, G, t] using hfamily')
  have hfixed :
      R ^ (2 * N) *
          Real.exp (-Cprofile * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        capacity * loss ^ 5 * volumeWeight := by
    simpa only [R, Cprofile, polyC112, N, L, G, Z, X, middle, capacity,
      loss, volumeNat, volumeWeight] using
        mme_dwz_q6_112_fixed_profile_usable_rate_lower tau C₀ t ht
  have hvolumeWeight : 0 ≤ volumeWeight := by
    dsimp [volumeWeight]
    positivity
  have hrate :
      R ^ (2 * N) *
          Real.exp (-Cprofile * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) * volumeWeight := by
    calc
      _ ≤ capacity * loss ^ 5 * volumeWeight := hfixed
      _ ≤ (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) * volumeWeight :=
        mul_le_mul_of_nonneg_right hcapacity' hvolumeWeight
  have hR : 0 ≤ R := by
    dsimp [R]
    apply pow_nonneg
    exact (by
      simp [componentBase, splitB]
      positivity)
  obtain ⟨q, a, b, c, hrestrict, hextract⟩ :=
    mme_Ctensor_one_half_family_to_six_finite_rate_of_capacity
      tau Cprofile R N A H volumeNat stars hR hH hHbound (by
        simpa only [volumeWeight] using hrate)
  refine ⟨q, a, b, c, hrestrict, ?_⟩
  let x : ℝ := Real.sqrt (((N + 1 : ℕ) : ℝ))
  let y : ℝ := Real.sqrt
    (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))
  have hcomponent :
      MME.DWZTable2Counts.component (12 : Fin 15) * m = 2 * N := by
    dsimp [MME.DWZTable2Counts.component, N, t]
    omega
  have hbase :
      (((componentBase tau (12 : Fin 15)) ^
          (MME.DWZTable2Counts.component (12 : Fin 15) * m)) ^ (6 : ℕ)) =
        R ^ (4 * N) := by
    rw [hcomponent]
    dsimp only [R]
    simp only [← pow_mul]
    congr 1
    omega
  have hNle :
      N + 1 ≤ MME.DWZTable2Counts.scale * m + 1 := by
    dsimp [N, t, MME.DWZTable2Counts.scale]
    omega
  have hsqrt : x ≤ y := by
    dsimp [x, y]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hNle)
  have hexp :
      Real.exp (-Cfinal * y) ≤ Real.exp (-Cfinal * x) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hextract' :
      R ^ (4 * N) * Real.exp (-Cfinal * x) ≤
        ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
    simpa only [Cfinal, x] using hextract
  change
    (((componentBase tau (12 : Fin 15)) ^
        (MME.DWZTable2Counts.component (12 : Fin 15) * m)) ^ (6 : ℕ)) *
      Real.exp (-Cfinal * y) ≤ _
  rw [hbase]
  exact (mul_le_mul_of_nonneg_left hexp (pow_nonneg hR _)).trans hextract'
