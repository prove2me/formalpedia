-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_continuous_iter_partial
-- name    : CompanionTheory.D.gk.admitted.Gard.continuous_iter_partial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:30:38.895622+00:00
-- url     : https://prove2.me/theorems/f2370fae-906c-42b2-b3cd-059df37f4b6d
-- title:
--   Gard: continuous iter partial
-- statement:
--   The Gard construction uses the continuous iter partial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GardingAvg.lean#L15-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GardingAvg.lean#L15-L32

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingAvg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set Filter
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.Gard
variable {P Q E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem CompanionTheory.D.gk.admitted.Gard.continuous_iter_partial (Φ : P × Q → E) (hΦ : ContDiff ℝ ∞ Φ) (k : ℕ) :
    Continuous fun p : P × Q => iteratedFDeriv ℝ k (fun y => Φ (y, p.2)) p.1 := by sorry
