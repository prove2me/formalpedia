-- Prove2me | Theorems.Thm_Deduction_zeroFree_of_rpow_window
-- name    : Deduction.zeroFree_of_rpow_window
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:13:25.67291+00:00
-- url     : https://prove2.me/theorems/5884ac64-1116-5052-8ca9-d1476a000c63
-- title:
--   Deduction: zero Free of rpow window
-- statement:
--   The Deduction construction uses the zero Free of rpow window property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean#L11-L14

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_lemmaL
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_WindowHypOfRpow
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ZeroFreeOfRpowWindow
import Theorems.Thm_Deduction_lemmaL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction

theorem Deduction.zeroFree_of_rpow_window (F : CharFamily) {θ δ C : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ)
    (h : ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)), Gm F y ≤ C * y ^ θ) :
    ZeroFree F θ := by sorry
