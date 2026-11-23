-- Prove2me | Theorems.Thm_DiscreteGroups_sglob_LConvKM_InvF_smul
-- name    : DiscreteGroups.sglob.LConvKM.InvF.smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:53.466434+00:00
-- url     : https://prove2.me/theorems/a40066a1-39bc-4703-817f-3c58b740d73d
-- title:
--   Inv F: smul
-- statement:
--   The Inv F construction uses the smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L18-L24

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

theorem DiscreteGroups.sglob.LConvKM.InvF.smul {G : Type*} [Group G] {ρ : Representation ℂ G M} {B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ}
    (hB : InvF ρ B) {r : ℝ} (hr : 0 ≤ r) : InvF ρ ((r : ℂ) • B) := by sorry
