-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G4_tri_mul_diag
-- name    : Formalism.FourierDecayAlt.P.G4.tri_mul_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:41:35.464442+00:00
-- url     : https://prove2.me/theorems/f905fcf8-6d93-4d35-a5cb-42b677e61774
-- title:
--   G4: tri mul diag
-- statement:
--   The G4 construction uses the tri mul diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L143-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L143-L149

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

theorem Formalism.FourierDecayAlt.P.G4.tri_mul_diag {d : ℕ} {p q : Matrix (Fin d) (Fin d) ℂ} (hp : ∀ i j, j < i → p i j = 0)
    (hq : ∀ i j, j < i → q i j = 0) (i : Fin d) : (p * q) i i = p i i * q i i := by sorry
