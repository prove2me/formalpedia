-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_of_contDiff
-- name    : CompanionTheory.D.Upq.Sm.SmOn.of_contDiff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:24:29.567272+00:00
-- url     : https://prove2.me/theorems/a99482d0-5f5d-4a29-9bd6-4ea715cdf2db
-- title:
--   Sm On: of cont Diff
-- statement:
--   The Sm On construction uses the of cont Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/SmoothVec.lean#L31-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/SmoothVec.lean#L31-L32

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
variable {E E' V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem CompanionTheory.D.Upq.Sm.SmOn.of_contDiff {A : Set E} {f : E → V} (hf : ContDiff ℝ ∞ f) : SmOn A f := by sorry
