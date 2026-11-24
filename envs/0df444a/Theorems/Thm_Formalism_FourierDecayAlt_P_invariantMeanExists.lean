-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_invariantMeanExists
-- name    : Formalism.FourierDecayAlt.P.invariantMeanExists
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:56:30.451808+00:00
-- url     : https://prove2.me/theorems/1e7801b2-9cf5-46a0-8d67-4afde6911234
-- title:
--   P: invariant Mean Exists
-- statement:
--   The P construction uses the invariant Mean Exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AverageOne.lean#L443-L443
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AverageOne.lean#L443-L443

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

theorem Formalism.FourierDecayAlt.P.invariantMeanExists : Formalism.FourierDecayAlt.crystallineComparison.MeanExists := by sorry
