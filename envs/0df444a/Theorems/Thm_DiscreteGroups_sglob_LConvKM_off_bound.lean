-- Prove2me | Theorems.Thm_DiscreteGroups_sglob_LConvKM_off_bound
-- name    : DiscreteGroups.sglob.LConvKM.off_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:56.93289+00:00
-- url     : https://prove2.me/theorems/4e61e839-eafe-49a7-af29-390d63db1704
-- title:
--   LConv KM: off bound
-- statement:
--   The LConv KM construction uses the off bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L243-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L243-L252

import Mathlib
import Definitions.Def_Development_DiscreteGroups_GlobalIrreducibility_LConvKMCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set ComplexConjugate
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open DiscreteGroups DiscreteGroups.sglob DiscreteGroups.sglob.LConvKM
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable {G : Type*} [Group G] (ρ : Representation ℂ G M) (c : ℕ → ℝ) (xs : ℕ → M)

theorem DiscreteGroups.sglob.LConvKM.off_bound (hsp : Submodule.span ℂ (Set.range xs) = ⊤) (hc : ∀ i, 0 < c i) (x y : M) :
    ∃ R, ∀ F ∈ capSet ρ c xs, ‖F x y‖ ≤ R := by sorry
