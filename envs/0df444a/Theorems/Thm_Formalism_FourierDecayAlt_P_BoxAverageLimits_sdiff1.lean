-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_sdiff1
-- name    : Formalism.FourierDecayAlt.P.BoxAverageLimits.sdiff1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:02.367353+00:00
-- url     : https://prove2.me/theorems/6b9ed595-2e91-46f9-bff6-3177ea60f517
-- title:
--   Box Average Limits: sdiff1
-- statement:
--   The Box Average Limits construction uses the sdiff1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AverageOne.lean#L115-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AverageOne.lean#L115-L143

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

theorem Formalism.FourierDecayAlt.P.BoxAverageLimits.sdiff1 (R : ℕ) (j : ι) :
    box ι R \ (box ι R).image (fun m => m + Pi.single j 1) ⊆
      Fintype.piFinset (Function.update (fun _ : ι => range R) j {0}) := by sorry
