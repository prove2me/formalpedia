-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_v_nonneg
-- name    : Formalism.FourierDecayAlt.P.Sz5.v_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:36.11708+00:00
-- url     : https://prove2.me/theorems/af100546-64f9-4f98-b836-81d4c5b1c5c4
-- title:
--   Sz5: v nonneg
-- statement:
--   The Sz5 construction uses the v nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L53-L59

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz5
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz5.v_nonneg (c : Cfg) (h : c.Ok) (i : ℕ) (hi : i + 1 ≤ c.k) : 0 ≤ c.v i := by sorry
