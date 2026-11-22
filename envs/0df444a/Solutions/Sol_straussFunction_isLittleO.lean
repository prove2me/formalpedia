-- Prove2me | solution 1 for straussFunction_isLittleO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:53:48.31682+00:00
-- url     : https://prove2.me/submissions/d1461f96-2137-4f64-bdb0-2cbf06714a35

import Definitions.Def_Polychromatic_Existence
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_LovaszFunction
import Theorems.Thm_straussFunction_le_of_forall_mBound
import Theorems.Thm_mBound_isLittleO


set_option autoImplicit true
open Finset
open Asymptotics Filter
theorem _root_.solution :
    ∃ f : ℕ → ℝ, f =o[atTop] (fun _ ↦ 1 : ℕ → ℝ) ∧ ∀ k ≥ 4,
      straussFunction k ≤ (3 + f k) * k * Real.log k := by
-- ANCHOR_END: straussFunction_isLittleO
  obtain ⟨f, hf, hfbound⟩ := mBound_isLittleO
  refine ⟨f, hf, fun k hk ↦ ?_⟩
  grw [straussFunction_le_of_forall_mBound hk]
  exact hfbound _ (by grind)
