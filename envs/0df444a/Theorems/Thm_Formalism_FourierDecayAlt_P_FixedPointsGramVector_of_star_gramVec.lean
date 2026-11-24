-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FixedPointsGramVector_of_star_gramVec
-- name    : Formalism.FourierDecayAlt.P.FixedPointsGramVector.of_star_gramVec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:11:24.559248+00:00
-- url     : https://prove2.me/theorems/6cbd18dc-154a-45c7-bf72-025eb0d2b322
-- title:
--   Fixed Points Gram Vector: of star gram Vec
-- statement:
--   The Fixed Points Gram Vector construction uses the of star gram Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FixedPointsGramVector.lean#L104-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FixedPointsGramVector.lean#L104-L107

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedFrameProperty
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedPointsGramVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FixedPointsGramVector
open C2x5 C2x6 C2x7 HermitianProjections
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.FixedPointsGramVector.of_star_gramVec (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    (Matrix.of fun i j => star (gramVec k r z z' γ i j)) = (gnB k r z z' γ)ᴴ := by sorry
