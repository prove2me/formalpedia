-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_apply_ds_conj
-- name    : CompanionTheory.D.Upq.Sm.apply_ds_conj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:42:57.165268+00:00
-- url     : https://prove2.me/theorems/1936ace6-40ca-4d45-92e9-4d5c3d19b666
-- title:
--   Sm: apply ds conj
-- statement:
--   The Sm construction uses the apply ds conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/UniformCoefficientBounds/CoefBoundUniform.lean#L53-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/UniformCoefficientBounds/CoefBoundUniform.lean#L53-L65

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_UniformCoefficientBounds_CoefBoundUniform
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set
open scoped ContDiff InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {G K : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}

theorem CompanionTheory.D.Upq.Sm.apply_ds_conj (hG : IsMatGroup G) (h : RepOn G σ) {k X : Mat n} (hk : k ∈ G)
    (hX : ∀ t, ex X t ∈ G) {v : H} (hv : IsSm G σ v) :
    (∀ t, ex (k * X * k⁻¹) t ∈ G) ∧ σ k (ds σ X v) = ds σ (k * X * k⁻¹) (σ k v) := by sorry
