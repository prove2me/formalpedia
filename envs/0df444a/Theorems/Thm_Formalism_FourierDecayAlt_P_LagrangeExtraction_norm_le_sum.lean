-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LagrangeExtraction_norm_le_sum
-- name    : Formalism.FourierDecayAlt.P.LagrangeExtraction.norm_le_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:16.372498+00:00
-- url     : https://prove2.me/theorems/d330e352-1108-46fb-acfe-d1db07bc9b03
-- title:
--   Lagrange Extraction: norm le sum
-- statement:
--   The Lagrange Extraction construction uses the norm le sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LagrangeExtraction.lean#L71-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LagrangeExtraction.lean#L71-L84

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LagrangeExtraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LagrangeExtraction
open Finset Polynomial Formalism.FourierDecayAlt.F7

theorem Formalism.FourierDecayAlt.P.LagrangeExtraction.norm_le_sum {V : Type} [SeminormedAddCommGroup V] [NormedSpace ℂ V] {K d : ℕ} (s : Fin K → ℂ)
    (W : ℕ → (Fin K → ℝ) → V) (grid : Fin K → Fin (d + 1) → ℝ) (hP : PolyStep K d s W)
    (hg : ∀ a, Function.Injective (grid a)) (y₀ : Fin K → ℝ) :
    (∏ a, ‖s a‖) * ‖W 0 y₀‖ ≤
      ∑ j : Fin K → Fin (d + 1), (∏ a, |lagCo (grid a) (j a)|) * ‖W K fun a => grid a (j a)‖ := by sorry
