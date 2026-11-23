-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_herm_plus
-- name    : Formalism.FourierDecayAlt.P.Wd4.herm_plus
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:34.557973+00:00
-- url     : https://prove2.me/theorems/d0861213-22ee-4aa7-958d-5768a1c349da
-- title:
--   Wd4: herm plus
-- statement:
--   The Wd4 construction uses the herm plus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L332-L340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean#L332-L340

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd4
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.W
variable {K B : Type} [Field K] [StarRing K] [Ring B] [StarRing B] [Algebra K B] [StarModule K B]
  {e : Fin 2 → Fin 2 → B}

theorem Formalism.FourierDecayAlt.P.Wd4.herm_plus (G Ta T0 Rh : M2 B) (hG : Gᴴ = G) (hGTa : (G * Ta)ᴴ = G * Ta)
    (hGT0 : (G * T0)ᴴ = G * T0) (hRh : Rhᴴ = Rh) (hc : Rh * G = G * Rh)
    (hex : Ta * T0 * Rh = Rh * T0 * Ta) : (G * Ta * (T0 * Rh))ᴴ = G * Ta * (T0 * Rh) := by sorry
