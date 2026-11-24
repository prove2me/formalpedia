-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_hasFDerivAt_orb
-- name    : CompanionTheory.ThKR.Mp.hasFDerivAt_orb
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:28:42.344885+00:00
-- url     : https://prove2.me/theorems/fa67ad5c-dfdc-42bc-92f8-fcbaca10bca2
-- title:
--   Mp: has FDeriv At orb
-- statement:
--   The Mp construction uses the has FDeriv At orb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/HasFDerivAtOrb.lean#L17-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/HasFDerivAtOrb.lean#L17-L68

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

theorem CompanionTheory.ThKR.Mp.hasFDerivAt_orb (hT : TopG l) (hN : NearOne l) (hD : SecDer l) {k : ℕ} (γ : (Fin k → ℝ) → G l)
    (hγ : Continuous γ) (hs : ∀ a b, Differentiable ℝ fun t => (pr (γ t) : Mat l) a b) (f : Sch l)
    (t₀ : Fin k → ℝ) :
    HasFDerivAt (orb γ f)
      (∑ a, ∑ b, (dm γ t₀ a b).smulRight (orb γ (Qd (Matrix.single a b 1) f) t₀)) t₀ := by sorry
