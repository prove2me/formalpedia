-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_kap_step
-- name    : Formalism.FourierDecayAlt.P.Wd10.kap_step
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:56.089572+00:00
-- url     : https://prove2.me/theorems/feaa9550-cd43-48d7-aa70-4c2267f83751
-- title:
--   Wd10: kap step
-- statement:
--   The Wd10 construction uses the kap step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PartialFlipCommuteDiagScalarOfFree.lean#L62-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PartialFlipCommuteDiagScalarOfFree.lean#L62-L74

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

theorem Formalism.FourierDecayAlt.P.Wd10.kap_step (q : K → K) (w : List (Letter K S)) (l : Letter K S) :
    ∀ L : List (Letter K S), Reg L (dl l).pt → qw q (L ++ w) (ypt l) ≠ 0 →
      qw q (L ++ w) (ypt l) / ph L (dl l).pt = qw q w (ypt l) * (L.map fun l' => fac l l').prod
  := by sorry
