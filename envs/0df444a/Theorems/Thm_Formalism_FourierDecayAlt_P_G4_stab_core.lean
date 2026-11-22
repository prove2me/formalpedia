-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G4_stab_core
-- name    : Formalism.FourierDecayAlt.P.G4.stab_core
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:53:43.885022+00:00
-- url     : https://prove2.me/theorems/f0e75ad2-7bf9-4072-9cb3-3333d99f9655
-- title:
--   G4: stab core
-- statement:
--   The G4 construction uses the stab core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L309-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L309-L320

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

theorem Formalism.FourierDecayAlt.P.G4.stab_core {d : ℕ} {l u : Matrix (Fin d) (Fin d) ℂ} (hu : IsUpperUni u) :
    l * wMat d * u = wMat d ↔ l = wMat d * u⁻¹ * wMat d := by sorry
