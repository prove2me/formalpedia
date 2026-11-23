-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G4_superSum_mul
-- name    : Formalism.FourierDecayAlt.P.G4.superSum_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:43.116808+00:00
-- url     : https://prove2.me/theorems/191cab2a-4892-4cd2-9969-3a4a337f89b6
-- title:
--   G4: super Sum mul
-- statement:
--   The G4 construction uses the super Sum mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L255-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L255-L273

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

theorem Formalism.FourierDecayAlt.P.G4.superSum_mul {n : ℕ} {p q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hp : IsUpperUni p)
    (hq : IsUpperUni q) : superSum (p * q) = superSum p + superSum q := by sorry
