-- Prove2me | Theorems.Thm_DiscreteGroups_sglob_LConvKM_extreme_exists_core
-- name    : DiscreteGroups.sglob.LConvKM.extreme_exists_core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:48.72155+00:00
-- url     : https://prove2.me/theorems/3e59444c-826b-4537-b7b2-5a6ddaa52a85
-- title:
--   LConv KM: extreme exists core
-- statement:
--   The LConv KM construction uses the extreme exists core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L374-L418
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L374-L418

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

theorem DiscreteGroups.sglob.LConvKM.extreme_exists_core {G : Type*} [Group G] (ρ : Representation ℂ G M)
    (hspan : ∃ s : Set M, s.Countable ∧ Submodule.span ℂ s = ⊤)
    (B₀ : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (h₀ : InvF ρ B₀) (f : M) (hf : B₀ f f ≠ 0) :
    ∃ B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, (InvF ρ B ∧ ∀ B' : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, InvF ρ B' → InvF ρ (B - B') →
      ∃ c : ℂ, ∀ x y, B' x y = c * B x y) ∧ B f f ≠ 0 := by sorry
