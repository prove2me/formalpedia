-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_kap_eq
-- name    : Formalism.FourierDecayAlt.P.Wd10.kap_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:51.996689+00:00
-- url     : https://prove2.me/theorems/ae5b3638-5d2c-4634-b3cd-359cb90fd637
-- title:
--   Wd10: kap eq
-- statement:
--   The Wd10 construction uses the kap eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PartialFlipCommuteDiagScalarOfFree.lean#L79-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PartialFlipCommuteDiagScalarOfFree.lean#L79-L85

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd10
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K S : Type} [Field K]

theorem Formalism.FourierDecayAlt.P.Wd10.kap_eq (q : K → K) (w : List (Letter K S)) :
    ∀ L : List (Letter K S), DualOK q w L → kap q w L = kapF q w L
  := by sorry
