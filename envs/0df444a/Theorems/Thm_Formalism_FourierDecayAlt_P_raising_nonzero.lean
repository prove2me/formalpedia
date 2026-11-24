-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_raising_nonzero
-- name    : Formalism.FourierDecayAlt.P.raising_nonzero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:17:37.08031+00:00
-- url     : https://prove2.me/theorems/b6da34a1-9ca9-448b-9e31-6149aad0129a
-- title:
--   P: raising nonzero
-- statement:
--   The P construction uses the raising nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IrreducibleCapelliModules.lean#L21-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IrreducibleCapelliModules.lean#L21-L21

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommonEigenvectors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HighestWeightPolynomials
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StarSumLemmas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BorderedDeterminants
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BranchingSystems
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ClosureOperators
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightMonotonicity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StrictBoxOrder
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IrreducibleCapelliModules
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt

theorem Formalism.FourierDecayAlt.P.raising_nonzero : Qr.RaiseNZ := by sorry
