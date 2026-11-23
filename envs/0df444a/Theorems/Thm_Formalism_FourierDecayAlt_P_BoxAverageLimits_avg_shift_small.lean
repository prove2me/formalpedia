-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_avg_shift_small
-- name    : Formalism.FourierDecayAlt.P.BoxAverageLimits.avg_shift_small
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:25.369806+00:00
-- url     : https://prove2.me/theorems/59f3f3cb-8f4b-4245-83af-5cf457eabb57
-- title:
--   Box Average Limits: avg shift small
-- statement:
--   The Box Average Limits construction uses the avg shift small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AverageOne.lean#L205-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AverageOne.lean#L205-L226

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AverageOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BoxAverageLimits
open Formalism.FourierDecayAlt.crystallineComparison
variable {Λ : Type} [AddCommGroup Λ] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem Formalism.FourierDecayAlt.P.BoxAverageLimits.avg_shift_small (e : ι → Λ) (c : ℕ → Λ) (g : Λ → ℂ) (B : ℝ) (hB : ∀ x, ‖g x‖ ≤ B) (j : ι) (n : ℕ) :
    ‖avg e c (fun x => g (x + e j)) n - avg e c g n‖ ≤ 2 * B / (n + 1) := by sorry
