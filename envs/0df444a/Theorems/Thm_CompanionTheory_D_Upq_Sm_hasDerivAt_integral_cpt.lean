-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_hasDerivAt_integral_cpt
-- name    : CompanionTheory.D.Upq.Sm.hasDerivAt_integral_cpt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:42:45.692797+00:00
-- url     : https://prove2.me/theorems/acb2f3b4-4c54-4b7f-9873-b457265613e1
-- title:
--   Sm: has Deriv At integral cpt
-- statement:
--   The Sm construction uses the has Deriv At integral cpt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/IntegralMemOfIsClosed.lean#L20-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/IntegralMemOfIsClosed.lean#L20-L37

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI CompanionTheory.D.Upq.ModEx
variable {α V : Type*} [TopologicalSpace α] [T2Space α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] [NormedAddCommGroup V] [NormedSpace ℝ V] {μ : Measure α}
  [IsFiniteMeasureOnCompacts μ]

theorem CompanionTheory.D.Upq.Sm.hasDerivAt_integral_cpt {F F' : ℝ → α → V} (hF : ∀ t, Continuous (F t))
    (hF' : Continuous fun p : ℝ × α => F' p.1 p.2) (hd : ∀ t a, HasDerivAt (F · a) (F' t a) t)
    {K : Set α} (hK : IsCompact K) (h0 : ∀ a ∉ K, F 0 a = 0)
    (h0' : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ a ∉ K, F' t a = 0) :
    HasDerivAt (fun t => ∫ a, F t a ∂μ) (∫ a, F' 0 a ∂μ) 0 := by sorry
