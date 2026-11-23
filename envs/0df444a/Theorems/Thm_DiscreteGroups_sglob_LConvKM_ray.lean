-- Prove2me | Theorems.Thm_DiscreteGroups_sglob_LConvKM_ray
-- name    : DiscreteGroups.sglob.LConvKM.ray
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:45:07.846128+00:00
-- url     : https://prove2.me/theorems/29a0871a-529b-4988-a75c-843571cd3643
-- title:
--   LConv KM: ray
-- statement:
--   The LConv KM construction uses the ray property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L263-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvKMCore.lean#L263-L370

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

theorem DiscreteGroups.sglob.LConvKM.ray (hsp : Submodule.span ℂ (Set.range xs) = ⊤) (hc : ∀ i, 0 < c i) (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)
    (hB : ev B ∈ (capSet ρ c xs).extremePoints ℝ) (B' : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)
    (h1 : InvF ρ B') (h2 : InvF ρ (B - B')) : ∃ k : ℂ, ∀ x y, B' x y = k * B x y := by sorry
