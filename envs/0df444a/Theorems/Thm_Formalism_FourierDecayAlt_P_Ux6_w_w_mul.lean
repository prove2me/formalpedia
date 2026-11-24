-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_w_w_mul
-- name    : Formalism.FourierDecayAlt.P.Ux6.w_w_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:35:31.725284+00:00
-- url     : https://prove2.me/theorems/63b8b029-abcf-41ce-ac5e-b1ca5406106d
-- title:
--   Ux6: w w mul
-- statement:
--   The Ux6 construction uses the w w mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L127-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L127-L128

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
variable {k j ρ : ℕ}

theorem Formalism.FourierDecayAlt.P.Ux6.w_w_mul (M : Matrix (Fin j) (Fin j) ℂ) : G.wMat j * (G.wMat j * M) = M := by sorry
