-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_cutoff_bound
-- name    : Formalism.FourierDecayAlt.P.cutoff_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:33.480369+00:00
-- url     : https://prove2.me/theorems/9a8941cb-2ce3-44db-9abc-b19e0820b8a0
-- title:
--   P: cutoff bound
-- statement:
--   The P construction uses the cutoff bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EnergyEstimateFromParts.lean#L36-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EnergyEstimateFromParts.lean#L36-L36

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2ConstMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EnergyEstimateFromParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.cutoff_bound : Formalism.FourierDecayAlt.LE.CutBound := by sorry
