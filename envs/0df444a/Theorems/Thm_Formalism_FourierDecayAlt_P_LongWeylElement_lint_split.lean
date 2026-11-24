-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lint_split
-- name    : Formalism.FourierDecayAlt.P.LongWeylElement.lint_split
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:17:09.819805+00:00
-- url     : https://prove2.me/theorems/fe3f1aa1-a57e-4bf1-938f-6e7d9b1a3e54
-- title:
--   Long Weyl Element: lint split
-- statement:
--   The Long Weyl Element construction uses the lint split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L649-L652
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L649-L652

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement

theorem Formalism.FourierDecayAlt.P.LongWeylElement.lint_split (r' : ℕ) (G : ℂ × (Fin r' → ℂ) → ℝ≥0∞) :
    ∫⁻ c : Fin (1 + r') → ℂ, G (splitC r' c) = ∫⁻ p : ℂ × (Fin r' → ℂ), G p := by sorry
