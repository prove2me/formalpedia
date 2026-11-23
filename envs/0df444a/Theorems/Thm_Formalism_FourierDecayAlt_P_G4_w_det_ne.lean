-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G4_w_det_ne
-- name    : Formalism.FourierDecayAlt.P.G4.w_det_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:46.074268+00:00
-- url     : https://prove2.me/theorems/8d3d4c29-e636-43e3-853b-5431311cb92b
-- title:
--   G4: w det ne
-- statement:
--   The G4 construction uses the w det ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L238-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L238-L241

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

theorem Formalism.FourierDecayAlt.P.G4.w_det_ne (d : ℕ) : (wMat d).det ≠ 0 := by sorry
