-- Prove2me | Theorems.Thm_DiscreteGroups_sglob_LConvKM_convex_capSet
-- name    : DiscreteGroups.sglob.LConvKM.convex_capSet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:34.429805+00:00
-- url     : https://prove2.me/theorems/8c607723-c2a9-4078-835c-ff75e37e8afd
-- title:
--   LConv KM: convex cap Set
-- statement:
--   The LConv KM construction uses the convex cap Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L186-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L186-L209

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

theorem DiscreteGroups.sglob.LConvKM.convex_capSet : Convex ℝ (capSet ρ c xs) := by sorry
