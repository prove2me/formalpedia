-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_exponent_sizes
-- name    : Formalism.FourierDecayAlt.P.exponent_sizes
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:36:58.186564+00:00
-- url     : https://prove2.me/theorems/e1241364-c35d-4ad2-879c-ebdbfc39dc56
-- title:
--   P: exponent sizes
-- statement:
--   The P construction uses the exponent sizes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CorollaryAOfPropositionA.lean#L447-L447
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CorollaryAOfPropositionA.lean#L447-L447

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.exponent_sizes : Formalism.FourierDecayAlt.Sz.EaSize := by sorry
