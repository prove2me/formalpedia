-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G4_stab_exists
-- name    : Formalism.FourierDecayAlt.P.G4.stab_exists
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:39:31.945669+00:00
-- url     : https://prove2.me/theorems/aaabe62c-7b7e-49a1-97a6-74031f0bb9c2
-- title:
--   G4: stab exists
-- statement:
--   The G4 construction uses the stab exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L334-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L334-L338

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

theorem Formalism.FourierDecayAlt.P.G4.stab_exists {d : ℕ} {l : Matrix (Fin d) (Fin d) ℂ} (hl : IsLowerUni l) :
    l⁻¹ * wMat d * (wMat d * l * wMat d) = wMat d := by sorry
