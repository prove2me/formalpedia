-- Prove2me | Theorems.Thm_DiscreteGroups_sglob_LConvKM_norm_le_polar
-- name    : DiscreteGroups.sglob.LConvKM.norm_le_polar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:42.981553+00:00
-- url     : https://prove2.me/theorems/2a2eb80a-cac1-4762-b467-ee3e6265a863
-- title:
--   LConv KM: norm le polar
-- statement:
--   The LConv KM construction uses the norm le polar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L66-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L66-L79

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

theorem DiscreteGroups.sglob.LConvKM.norm_le_polar (herm : ∀ x y, (starRingEnd ℂ) (B x y) = B y x) (psd : ∀ x, 0 ≤ (B x x).re)
    (x y : M) :
    4 * ‖B x y‖ ≤ (B (x + y) (x + y)).re + (B (x - y) (x - y)).re
      + (B (x + Complex.I • y) (x + Complex.I • y)).re + (B (x - Complex.I • y) (x - Complex.I • y)).re := by sorry
