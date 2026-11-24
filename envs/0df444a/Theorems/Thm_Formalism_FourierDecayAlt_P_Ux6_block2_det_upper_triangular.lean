-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_block2_det_upper_triangular
-- name    : Formalism.FourierDecayAlt.P.Ux6.block2_det_upper_triangular
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:50:45.693008+00:00
-- url     : https://prove2.me/theorems/44677a3e-09bb-4605-9aea-d1997f296851
-- title:
--   Ux6: block2 det upper triangular
-- statement:
--   The Ux6 construction uses the block2 det upper triangular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L250-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L250-L253

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

theorem Formalism.FourierDecayAlt.P.Ux6.block2_det_upper_triangular {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ)
    (D : Matrix (Fin s) (Fin s) ℂ) : (blk2 A B 0 D).det = A.det * D.det := by sorry
