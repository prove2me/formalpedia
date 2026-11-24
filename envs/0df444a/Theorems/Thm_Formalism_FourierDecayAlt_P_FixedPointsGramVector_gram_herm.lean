-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FixedPointsGramVector_gram_herm
-- name    : Formalism.FourierDecayAlt.P.FixedPointsGramVector.gram_herm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:11:15.983312+00:00
-- url     : https://prove2.me/theorems/f2f564cc-7f57-4b9a-aa0e-eac8c575f06f
-- title:
--   Fixed Points Gram Vector: gram herm
-- statement:
--   The Fixed Points Gram Vector construction uses the gram herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FixedPointsGramVector.lean#L130-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FixedPointsGramVector.lean#L130-L133

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

theorem Formalism.FourierDecayAlt.P.FixedPointsGramVector.gram_herm (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    ((gnB k r z z' γ)ᴴ * Hpk k r * gnB k r z z' γ)ᴴ = (gnB k r z z' γ)ᴴ * Hpk k r * gnB k r z z' γ := by sorry
