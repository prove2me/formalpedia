-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_contDiff_dm
-- name    : CompanionTheory.ThKR.Mp.contDiff_dm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:28:51.352511+00:00
-- url     : https://prove2.me/theorems/dcbc2adc-be34-4292-bf9b-9249e32592f8
-- title:
--   Mp: cont Diff dm
-- statement:
--   The Mp construction uses the cont Diff dm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/HasFDerivAtOrb.lean#L70-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/HasFDerivAtOrb.lean#L70-L85

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MpFOne
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_HasFDerivAtOrb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real ContDiff
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]

theorem CompanionTheory.ThKR.Mp.contDiff_dm {k : ℕ} (γ : (Fin k → ℝ) → G l)
    (hs : ∀ a b, ContDiff ℝ ∞ fun t => (pr (γ t) : Mat l) a b) (a b : l ⊕ l) (n : ℕ) :
    ContDiff ℝ n fun t => dm γ t a b := by sorry
