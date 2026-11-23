-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Cauchy_iteratedDeriv_ofReal
-- name    : Formalism.FourierDecayAlt.P.Cauchy.iteratedDeriv_ofReal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:08.8212+00:00
-- url     : https://prove2.me/theorems/44d833b1-9025-45b6-a4ef-061fe9079bd7
-- title:
--   Cauchy: iterated Deriv of Real
-- statement:
--   The Cauchy construction uses the iterated Deriv of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Cauchy.lean#L7-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Cauchy.lean#L7-L33

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Cauchy
open Complex Metric Set

theorem Formalism.FourierDecayAlt.P.Cauchy.iteratedDeriv_ofReal {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F U)
    {f : ℝ → ℝ} (hmem : ∀ x : ℝ, (x : ℂ) ∈ U) (hfF : ∀ x : ℝ, F x = f x) (p : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv p F) U ∧
      ∀ x : ℝ, iteratedDeriv p F x = (iteratedDeriv p f x : ℝ) := by sorry
