-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G4_superSum_inv
-- name    : Formalism.FourierDecayAlt.P.G4.superSum_inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:41:39.862727+00:00
-- url     : https://prove2.me/theorems/9a66bbe0-364e-4b0a-82e9-41dd3b6c953d
-- title:
--   G4: super Sum inv
-- statement:
--   The G4 construction uses the super Sum inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L280-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L280-L282

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

theorem Formalism.FourierDecayAlt.P.G4.superSum_inv {n : ℕ} {u : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hu : IsUpperUni u) :
    superSum u⁻¹ + superSum u = 0 := by sorry
