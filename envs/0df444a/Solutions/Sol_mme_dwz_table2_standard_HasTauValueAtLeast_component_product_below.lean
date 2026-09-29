-- Prove2me | solution 1 for mme_dwz_table2_standard_HasTauValueAtLeast_component_product_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T12:35:19.74869+00:00
-- url     : https://prove2.me/submissions/52e1f058-c62b-457a-8278-5580adc795bf

import Mathlib.Tactic
import Definitions.Def_mme_dwz_table2_standard_obj
import Definitions.Def_mme_dwz_square_data
import Theorems.Thm_mme_dwz_square_componentBase_pos
import Theorems.Thm_mme_finite_kronFin_HasTauValueAtLeast_product_below

open MME BigOperators
open MME.DWZSquare
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (m : ℕ) (tau : ℝ)
    (localTarget : Fin 15 → ℝ)
    (htarget : ∀ s, 0 ≤ localTarget s)
    (hstrict : ∀ s,
      localTarget s <
        (componentBase tau s) ^
          (MME.DWZTable2Counts.component s * m))
    (hlocal : ∀ (s : Fin 15) (W : ℝ),
      0 ≤ W →
      W <
        (componentBase tau s) ^
          (MME.DWZTable2Counts.component s * m) →
      HasTauValueAtLeast (restrictedComponentPower K s m) tau W) :
    HasTauValueAtLeast (dwzTable2StandardObj K m) tau
      (∏ s, localTarget s) := by
  let endpoint : Fin 15 → ℝ := fun s ↦
    (componentBase tau s) ^
      (MME.DWZTable2Counts.component s * m)
  let localBase : Fin 15 → ℝ := fun s ↦
    (localTarget s + endpoint s) / 2
  have hendpoint : ∀ s, 0 < endpoint s := by
    intro s
    exact pow_pos (mme_dwz_square_componentBase_pos tau s) _
  have hbase : ∀ s, 0 < localBase s := by
    intro s
    dsimp only [localBase]
    have he := hendpoint s
    have ht := htarget s
    linarith
  have htargetBase : ∀ s, localTarget s < localBase s := by
    intro s
    dsimp only [localBase]
    have hs := hstrict s
    change localTarget s < endpoint s at hs
    linarith
  have hbaseEndpoint : ∀ s, localBase s < endpoint s := by
    intro s
    dsimp only [localBase]
    have hs := hstrict s
    change localTarget s < endpoint s at hs
    linarith
  have hvalue : ∀ s,
      HasTauValueAtLeast (restrictedComponentPower K s m) tau
        (localBase s) := by
    intro s
    apply hlocal s (localBase s) (hbase s).le
    simpa only [endpoint] using hbaseEndpoint s
  simpa only [dwzTable2StandardObj] using
    mme_finite_kronFin_HasTauValueAtLeast_product_below
      (fun s : Fin 15 ↦ restrictedComponentPower K s m)
      tau localBase localTarget hbase htarget htargetBase hvalue
