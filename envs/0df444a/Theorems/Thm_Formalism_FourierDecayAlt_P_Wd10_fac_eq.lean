-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_fac_eq
-- name    : Formalism.FourierDecayAlt.P.Wd10.fac_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:07.434806+00:00
-- url     : https://prove2.me/theorems/9d3bb329-d6e8-4c6b-8614-0e37fc6909bb
-- title:
--   Wd10: fac eq
-- statement:
--   The Wd10 construction uses the fac eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PartialFlipCommuteDiagScalarOfFree.lean#L33-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PartialFlipCommuteDiagScalarOfFree.lean#L33-L60

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

theorem Formalism.FourierDecayAlt.P.Wd10.fac_eq (l l' : Letter K S) (hr : RegL l' (dl l).pt) (hg : gq l' (ypt l) ≠ 0) :
    gq l' (ypt l) / hp l' (dl l).pt = fac l l' := by sorry
