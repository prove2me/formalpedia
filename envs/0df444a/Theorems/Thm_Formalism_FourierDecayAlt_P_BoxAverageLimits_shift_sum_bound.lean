-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_shift_sum_bound
-- name    : Formalism.FourierDecayAlt.P.BoxAverageLimits.shift_sum_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:01.108136+00:00
-- url     : https://prove2.me/theorems/c06b1e59-67b2-4df0-9af4-cdddcde81e7a
-- title:
--   Box Average Limits: shift sum bound
-- statement:
--   The Box Average Limits construction uses the shift sum bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AverageOne.lean#L171-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AverageOne.lean#L171-L203

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

theorem Formalism.FourierDecayAlt.P.BoxAverageLimits.shift_sum_bound (R : ℕ) (j : ι) (G : (ι → ℕ) → ℂ) (B : ℝ) (hB : ∀ m, ‖G m‖ ≤ B) :
    ‖∑ m ∈ box ι R, G (m + Pi.single j 1) - ∑ m ∈ box ι R, G m‖ ≤
      2 * B * R ^ (Fintype.card ι - 1) := by sorry
