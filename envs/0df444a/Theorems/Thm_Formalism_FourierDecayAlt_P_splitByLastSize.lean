-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_splitByLastSize
-- name    : Formalism.FourierDecayAlt.P.splitByLastSize
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:00.287806+00:00
-- url     : https://prove2.me/theorems/396a17cf-bf65-4af8-8eef-b3eb1d693687
-- title:
--   P: split By Last Size
-- statement:
--   The P construction uses the split By Last Size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositiveSemidefinitePullback.lean#L120-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositiveSemidefinitePullback.lean#L120-L130

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveSemidefinitePullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Matrix Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
open Classical

theorem Formalism.FourierDecayAlt.P.splitByLastSize : Formalism.FourierDecayAlt.TB.SplitBySize := by sorry
