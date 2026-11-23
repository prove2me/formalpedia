-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G4_lowerUni_conj
-- name    : Formalism.FourierDecayAlt.P.G4.lowerUni_conj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:19.880161+00:00
-- url     : https://prove2.me/theorems/99e11b1d-868d-496c-b9e9-c5c36bdd0da6
-- title:
--   G4: lower Uni conj
-- statement:
--   The G4 construction uses the lower Uni conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L243-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L243-L247

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

theorem Formalism.FourierDecayAlt.P.G4.lowerUni_conj {d : ℕ} {u : Matrix (Fin d) (Fin d) ℂ} (hu : IsUpperUni u) :
    IsLowerUni (wMat d * u * wMat d) := by sorry
