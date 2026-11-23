-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G4_lower_inv_mul
-- name    : Formalism.FourierDecayAlt.P.G4.lower_inv_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:38.160203+00:00
-- url     : https://prove2.me/theorems/6fc771b0-c0ce-4eee-8f12-60e36115a765
-- title:
--   G4: lower inv mul
-- statement:
--   The G4 construction uses the lower inv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L183-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L183-L184

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

theorem Formalism.FourierDecayAlt.P.G4.lower_inv_mul {d : ℕ} {l : Matrix (Fin d) (Fin d) ℂ} (hl : IsLowerUni l) : l⁻¹ * l = 1 := by sorry
