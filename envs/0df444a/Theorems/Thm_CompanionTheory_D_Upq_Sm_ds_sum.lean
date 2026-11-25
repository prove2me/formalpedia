-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_ds_sum
-- name    : CompanionTheory.D.Upq.Sm.ds_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:42:51.985173+00:00
-- url     : https://prove2.me/theorems/800a2d1c-c262-5206-915e-fa2fd4ac809b
-- title:
--   Sm: ds sum
-- statement:
--   The Sm construction uses the ds sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/UniformCoefficientBounds/CoefBoundUniform.lean#L37-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/UniformCoefficientBounds/CoefBoundUniform.lean#L37-L45

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

theorem CompanionTheory.D.Upq.Sm.ds_sum (h : RepOn G σ) {X : Mat n} (hX : ∀ t, ex X t ∈ G) {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) {b : ι → H} (hb : ∀ i, IsSm G σ (b i)) :
    ds σ X (∑ i ∈ s, c i • b i) = ∑ i ∈ s, c i • ds σ X (b i) := by sorry
