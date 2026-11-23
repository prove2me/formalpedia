-- Prove2me | Theorems.Thm_DiscreteGroups_sglob_LConvKM_re_add_le
-- name    : DiscreteGroups.sglob.LConvKM.re_add_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:40.37383+00:00
-- url     : https://prove2.me/theorems/2773154c-3215-4311-8965-0763c573d33a
-- title:
--   LConv KM: re add le
-- statement:
--   The LConv KM construction uses the re add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L46-L50

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
variable (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)

theorem DiscreteGroups.sglob.LConvKM.re_add_le (psd : ∀ x, 0 ≤ (B x x).re) (x y : M) :
    (B (x + y) (x + y)).re ≤ 2 * (B x x).re + 2 * (B y y).re := by sorry
