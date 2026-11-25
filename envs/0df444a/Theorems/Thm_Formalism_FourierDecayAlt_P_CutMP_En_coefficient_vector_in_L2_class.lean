-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_En_coefficient_vector_in_L2_class
-- name    : Formalism.FourierDecayAlt.P.CutMP.En.coefficient_vector_in_L2_class
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:40:21.409221+00:00
-- url     : https://prove2.me/theorems/afec3581-c205-4d90-ae99-c94d7cc7d309
-- title:
--   En: coefficient vector in L2 class
-- statement:
--   The En construction uses the coefficient vector in L2 class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutEnCVInCC.lean#L30-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutEnCVInCC.lean#L30-L40

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnCVInCC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.En

theorem Formalism.FourierDecayAlt.P.CutMP.En.coefficient_vector_in_L2_class : CVInCC := by sorry
