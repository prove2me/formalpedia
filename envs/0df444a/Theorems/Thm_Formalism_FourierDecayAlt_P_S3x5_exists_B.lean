-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_exists_B
-- name    : Formalism.FourierDecayAlt.P.S3x5.exists_B
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:43:20.174748+00:00
-- url     : https://prove2.me/theorems/109a1447-eba5-4728-b7c2-9fbc761175dc
-- title:
--   S3x5: exists B
-- statement:
--   The S3x5 construction uses the exists B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L598-L662
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L598-L662

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Matrix
variable {K : Type} [Field K] [Fintype K] [StarRing K]
omit [Fintype K]

theorem Formalism.FourierDecayAlt.P.S3x5.exists_B (a : ℕ) (T : Matrix (Fin a) (Fin a) K) (hT : Tᴴ = T) :
    ∃ B : Matrix (Fin a) (Fin (a - T.rank)) K,
      ∀ D : Matrix (Fin (a - T.rank)) (Fin (a - T.rank)) K,
        IsUnit (Matrix.fromBlocks T B Bᴴ D).det := by sorry
