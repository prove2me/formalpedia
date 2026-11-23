-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G4_upperUni_mul
-- name    : Formalism.FourierDecayAlt.P.G4.upperUni_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:41:35.190347+00:00
-- url     : https://prove2.me/theorems/d09fb8b7-ba52-46c6-98c1-f7868b5fa086
-- title:
--   G4: upper Uni mul
-- statement:
--   The G4 construction uses the upper Uni mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L162-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L162-L164

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

theorem Formalism.FourierDecayAlt.P.G4.upperUni_mul {d : ℕ} {p q : Matrix (Fin d) (Fin d) ℂ} (hp : IsUpperUni p) (hq : IsUpperUni q) :
    IsUpperUni (p * q) := by sorry
