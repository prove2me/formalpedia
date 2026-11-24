-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_zj_mul
-- name    : Formalism.FourierDecayAlt.P.Ux4.zj_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:28:17.983824+00:00
-- url     : https://prove2.me/theorems/0f6270cf-53f2-414b-a5d4-3e87e553853f
-- title:
--   Ux4: zj mul
-- statement:
--   The Ux4 construction uses the zj mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L219-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L219-L229

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux4

theorem Formalism.FourierDecayAlt.P.Ux4.zj_mul {p s : ℕ} (a : Fin s → Fin p → ℂ) (b : Fin p → Fin s → ℂ) (H : Matrix (Fin p) (Fin p) ℂ)
    (Z q : Matrix (Fin s) (Fin s) ℂ) :
    Zj a b H (Z * q) = Zj a b H Z * ((blk2 1 (Matrix.of b) 0 1)⁻¹ * blk2 1 0 0 q * blk2 1 (Matrix.of b) 0 1) := by sorry
