-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_bdd_shift
-- name    : Formalism.FourierDecayAlt.P.BoxAverageLimits.bdd_shift
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:31.145822+00:00
-- url     : https://prove2.me/theorems/9a7d64c3-d122-4d17-9e05-c7bf919aa257
-- title:
--   Box Average Limits: bdd shift
-- statement:
--   The Box Average Limits construction uses the bdd shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AverageOne.lean#L244-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AverageOne.lean#L244-L245

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

theorem Formalism.FourierDecayAlt.P.BoxAverageLimits.bdd_shift {g : Λ → ℂ} (hg : Bdd g) (σ : Λ) : Bdd (fun x => g (x + σ)) := by sorry
