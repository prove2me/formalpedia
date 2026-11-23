-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G4_subSum_conj
-- name    : Formalism.FourierDecayAlt.P.G4.subSum_conj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:39:50.240375+00:00
-- url     : https://prove2.me/theorems/6fba0b89-89a4-43b5-bf03-6e70fbd85fc7
-- title:
--   G4: sub Sum conj
-- statement:
--   The G4 construction uses the sub Sum conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L284-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L284-L289

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt.G
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G4

theorem Formalism.FourierDecayAlt.P.G4.subSum_conj {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    subSum (wMat (n + 1) * M * wMat (n + 1)) = superSum M := by sorry
