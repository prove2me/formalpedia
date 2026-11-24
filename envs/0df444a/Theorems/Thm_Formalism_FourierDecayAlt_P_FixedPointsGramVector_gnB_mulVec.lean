-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FixedPointsGramVector_gnB_mulVec
-- name    : Formalism.FourierDecayAlt.P.FixedPointsGramVector.gnB_mulVec
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:11:28.724069+00:00
-- url     : https://prove2.me/theorems/390655e4-ffd3-49db-9ed9-e8af0c5b6423
-- title:
--   Fixed Points Gram Vector: gn B mul Vec
-- statement:
--   The Fixed Points Gram Vector construction uses the gn B mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FixedPointsGramVector.lean#L113-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FixedPointsGramVector.lean#L113-L117

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

theorem Formalism.FourierDecayAlt.P.FixedPointsGramVector.gnB_mulVec (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    gnB k r z z' γ *ᵥ c = ∑ i, c i • gramVec k r z z' γ i := by sorry
