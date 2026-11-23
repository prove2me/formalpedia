-- Prove2me | Theorems.Thm_DiscreteGroups_sglob_LConvKM_isClosed_capSet
-- name    : DiscreteGroups.sglob.LConvKM.isClosed_capSet
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:39.689121+00:00
-- url     : https://prove2.me/theorems/8ec5ba5b-9a42-4310-b37b-26e03d6bbca3
-- title:
--   LConv KM: is Closed cap Set
-- statement:
--   The LConv KM construction uses the is Closed cap Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L174-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L174-L184

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

theorem DiscreteGroups.sglob.LConvKM.isClosed_capSet : IsClosed (capSet ρ c xs) := by sorry
