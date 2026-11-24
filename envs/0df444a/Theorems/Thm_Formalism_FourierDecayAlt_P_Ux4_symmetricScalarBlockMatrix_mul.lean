-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_symmetricScalarBlockMatrix_mul
-- name    : Formalism.FourierDecayAlt.P.Ux4.symmetricScalarBlockMatrix_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:11:01.335944+00:00
-- url     : https://prove2.me/theorems/314625cf-269f-407b-b219-eaa62692b24a
-- title:
--   Ux4: symmetric Scalar Block Matrix mul
-- statement:
--   The Ux4 construction uses the symmetric Scalar Block Matrix mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L210-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L210-L213

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

theorem Formalism.FourierDecayAlt.P.Ux4.symmetricScalarBlockMatrix_mul {p s : ℕ} (A A' : Matrix (Fin p) (Fin p) ℂ) (B B' : Matrix (Fin p) (Fin s) ℂ)
    (C C' : Matrix (Fin s) (Fin p) ℂ) (D D' : Matrix (Fin s) (Fin s) ℂ) :
    blk2 A B C D * blk2 A' B' C' D' = blk2 (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by sorry
