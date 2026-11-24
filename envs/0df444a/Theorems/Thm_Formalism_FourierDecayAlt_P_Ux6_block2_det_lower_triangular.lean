-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_block2_det_lower_triangular
-- name    : Formalism.FourierDecayAlt.P.Ux6.block2_det_lower_triangular
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:54:41.01187+00:00
-- url     : https://prove2.me/theorems/78fcceed-fd18-4fe7-be61-9cb0d88c8864
-- title:
--   Ux6: block2 det lower triangular
-- statement:
--   The Ux6 construction uses the block2 det lower triangular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L245-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L245-L248

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux6

theorem Formalism.FourierDecayAlt.P.Ux6.block2_det_lower_triangular {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (C : Matrix (Fin s) (Fin p) ℂ)
    (D : Matrix (Fin s) (Fin s) ℂ) : (blk2 A 0 C D).det = A.det * D.det := by sorry
