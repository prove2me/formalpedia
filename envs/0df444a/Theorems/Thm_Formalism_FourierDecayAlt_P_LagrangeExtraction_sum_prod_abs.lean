-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LagrangeExtraction_sum_prod_abs
-- name    : Formalism.FourierDecayAlt.P.LagrangeExtraction.sum_prod_abs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:11.730116+00:00
-- url     : https://prove2.me/theorems/de39c8f4-1157-498d-a37a-636f874f4414
-- title:
--   Lagrange Extraction: sum prod abs
-- statement:
--   The Lagrange Extraction construction uses the sum prod abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LagrangeExtraction.lean#L64-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LagrangeExtraction.lean#L64-L69

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

theorem Formalism.FourierDecayAlt.P.LagrangeExtraction.sum_prod_abs {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) :
    ∑ j : Fin K → Fin (d + 1), ∏ a, |lagCo (grid a) (j a)| = ∏ a, ∑ i, |lagCo (grid a) i| := by sorry
