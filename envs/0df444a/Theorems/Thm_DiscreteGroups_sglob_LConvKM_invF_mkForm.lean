-- Prove2me | Theorems.Thm_DiscreteGroups_sglob_LConvKM_invF_mkForm
-- name    : DiscreteGroups.sglob.LConvKM.invF_mkForm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:26.944796+00:00
-- url     : https://prove2.me/theorems/b0d95f10-0627-48bf-b88b-cfff0d6fd489
-- title:
--   LConv KM: inv F mk Form
-- statement:
--   The LConv KM construction uses the inv F mk Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L168-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L168-L169

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

theorem DiscreteGroups.sglob.LConvKM.invF_mkForm {F : M → M → ℂ} (h : F ∈ capSet ρ c xs) : InvF ρ (mkForm F h.1.1.1.1) := by sorry
