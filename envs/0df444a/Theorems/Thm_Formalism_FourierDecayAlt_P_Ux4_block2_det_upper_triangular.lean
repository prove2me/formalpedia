-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block2_det_upper_triangular
-- name    : Formalism.FourierDecayAlt.P.Ux4.block2_det_upper_triangular
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:49:54.898801+00:00
-- url     : https://prove2.me/theorems/1081eccd-4cdc-4c91-b305-2a76e45d65cc
-- title:
--   Ux4: block2 det upper triangular
-- statement:
--   The Ux4 construction uses the block2 det upper triangular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L215-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L215-L217

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

theorem Formalism.FourierDecayAlt.P.Ux4.block2_det_upper_triangular {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ) (D : Matrix (Fin s) (Fin s) ℂ) :
    (blk2 A B 0 D).det = A.det * D.det := by sorry
