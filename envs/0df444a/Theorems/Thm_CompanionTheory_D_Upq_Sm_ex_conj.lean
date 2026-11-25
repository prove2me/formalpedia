-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_ex_conj
-- name    : CompanionTheory.D.Upq.Sm.ex_conj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:43:27.136646+00:00
-- url     : https://prove2.me/theorems/89fe1782-bdfe-41e4-82d9-650a58253a7c
-- title:
--   Sm: ex conj
-- statement:
--   The Sm construction uses the ex conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/UniformCoefficientBounds/CoefBoundUniform.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/UniformCoefficientBounds/CoefBoundUniform.lean#L47-L51

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

theorem CompanionTheory.D.Upq.Sm.ex_conj (hG : IsMatGroup G) {k : Mat n} (hk : k ∈ G) (X : Mat n) (t : ℝ) :
    ex (k * X * k⁻¹) t = k * ex X t * k⁻¹ := by sorry
