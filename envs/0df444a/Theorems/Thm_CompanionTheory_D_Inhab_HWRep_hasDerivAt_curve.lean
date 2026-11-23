-- Prove2me | Theorems.Thm_CompanionTheory_D_Inhab_HWRep_hasDerivAt_curve
-- name    : CompanionTheory.D.Inhab.HWRep.hasDerivAt_curve
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:07:11.58067+00:00
-- url     : https://prove2.me/theorems/902e1ce0-0db4-41ca-8b4d-bbaad35efd26
-- title:
--   HWRep: has Deriv At curve
-- statement:
--   The HWRep construction uses the has Deriv At curve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/NonemptyRepresentations/HWRepD.lean#L26-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/NonemptyRepresentations/HWRepD.lean#L26-L41

import Definitions.Def_CompanionTheory_HarishChandraModules_NonemptyRepresentations_NonemptyOfAntitone
import Definitions.Def_CompanionTheory_HarishChandraModules_NonemptyRepresentations_HWRepD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Inhab CompanionTheory.D.Inhab.HWRep
variable {k : ℕ} {ν : Fin k → ℤ} (R : HWRep k ν)

theorem CompanionTheory.D.Inhab.HWRep.hasDerivAt_curve (γ : ℝ → Matrix (Fin k) (Fin k) ℂ) (Y : Matrix (Fin k) (Fin k) ℂ) (h0 : γ 0 = 1)
    (hγ : ∀ a b, HasDerivAt (fun t => γ t a b) (Y a b) 0) (v : R.I → ℂ) :
    HasDerivAt (fun t => R.ρ (γ t) *ᵥ v) (R.D Y *ᵥ v) 0 := by sorry
