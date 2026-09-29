-- Prove2me | solution 1 for mme_CW_2376_target_joint_table_marginal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T23:25:28.599203+00:00
-- url     : https://prove2.me/submissions/c50a7b44-4b29-423b-91df-509aa3e939a7

import Definitions.Def_mme_CW_2376_marginal_joint_tables

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem solution
    (m : ℕ) (i : Fin 3) (r : Fin 5) :
    (∑ sigma : {sigma : CW2376SupportedJointType // sigma.1 i = r},
      cw2376TargetJointTable m sigma.1) =
        cw2376MarginalMultiplicity m r := by
  have hfin :
      (∑ sigma ∈ cw2376TargetJointTypes,
        if sigma i = r then cw2376ProfileMultiplicity m sigma else 0) =
        cw2376MarginalMultiplicity m r := by
    have hscaleProfile (sigma : Fin 3 → Fin 5) :
        cw2376ProfileMultiplicity m sigma =
          cw2376ProfileMultiplicity 1 sigma * m := by
      by_cases hs : sigma ∈ cw2376ScalarTypes
      · simp [cw2376ProfileMultiplicity, hs]
      by_cases hr : sigma ∈ cw2376RectTypes
      · simp [cw2376ProfileMultiplicity, hs, hr]
      by_cases hc : sigma ∈ cw2376CentralTypes
      · simp [cw2376ProfileMultiplicity, hs, hr, hc]
      by_cases hd : sigma ∈ cw2376CoupledTypes
      · simp [cw2376ProfileMultiplicity, hs, hr, hc, hd]
      · simp [cw2376ProfileMultiplicity, hs, hr, hc, hd]
    have hscaleMarginal (s : Fin 5) :
        cw2376MarginalMultiplicity m s =
          cw2376MarginalMultiplicity 1 s * m := by
      fin_cases s <;> norm_num [cw2376MarginalMultiplicity]
    have hunit : ∀ j : Fin 3, ∀ s : Fin 5,
        (∑ sigma ∈ cw2376TargetJointTypes,
          if sigma j = s then cw2376ProfileMultiplicity 1 sigma else 0) =
          cw2376MarginalMultiplicity 1 s := by
      decide
    calc
      (∑ sigma ∈ cw2376TargetJointTypes,
          if sigma i = r then cw2376ProfileMultiplicity m sigma else 0) =
          ∑ sigma ∈ cw2376TargetJointTypes,
            (if sigma i = r then
              cw2376ProfileMultiplicity 1 sigma else 0) * m := by
        apply Finset.sum_congr rfl
        intro sigma hsigma
        by_cases h : sigma i = r
        · simp [h, hscaleProfile]
        · simp [h]
      _ = (∑ sigma ∈ cw2376TargetJointTypes,
            if sigma i = r then
              cw2376ProfileMultiplicity 1 sigma else 0) * m := by
        rw [Finset.sum_mul]
      _ = cw2376MarginalMultiplicity 1 r * m := by
        rw [hunit i r]
      _ = cw2376MarginalMultiplicity m r := (hscaleMarginal r).symm
  calc
    (∑ sigma : {sigma : CW2376SupportedJointType // sigma.1 i = r},
        cw2376TargetJointTable m sigma.1) =
        ∑ sigma : CW2376SupportedJointType,
          if sigma.1 i = r then cw2376TargetJointTable m sigma else 0 := by
      symm
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype
        (p := fun sigma : CW2376SupportedJointType => sigma.1 i = r)
        ((Finset.univ : Finset CW2376SupportedJointType).filter
          (fun sigma => sigma.1 i = r))
        (fun sigma => by simp)
        (fun sigma => cw2376TargetJointTable m sigma)
    _ = ∑ sigma ∈ cw2376TargetJointTypes,
          if sigma i = r then cw2376ProfileMultiplicity m sigma else 0 := by
      rw [Finset.sum_subtype cw2376TargetJointTypes
        (fun sigma => Iff.rfl)]
      rfl
    _ = cw2376MarginalMultiplicity m r := hfin
