-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_avg_real_nonneg
-- name    : Formalism.FourierDecayAlt.P.BoxAverageLimits.avg_real_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:32.074801+00:00
-- url     : https://prove2.me/theorems/3a0ce2e9-18ad-4288-940e-4fb21077e40d
-- title:
--   Box Average Limits: avg real nonneg
-- statement:
--   The Box Average Limits construction uses the avg real nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AverageOne.lean#L82-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AverageOne.lean#L82-L89

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

theorem Formalism.FourierDecayAlt.P.BoxAverageLimits.avg_real_nonneg (e : ι → Λ) (c : ℕ → Λ) (g : Λ → ℂ)
    (hg : ∀ x, 0 ≤ (g x).re ∧ (g x).im = 0) (n : ℕ) :
    0 ≤ (avg e c g n).re ∧ (avg e c g n).im = 0 := by sorry
