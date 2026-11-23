-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_degreeOf_prod_linear_le
-- name    : Formalism.FourierDecayAlt.P.LEx2.degreeOf_prod_linear_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:13.815321+00:00
-- url     : https://prove2.me/theorems/bf1d68c3-36de-444b-8f1d-a90c8885fea1
-- title:
--   LEx2: degree Of prod linear le
-- statement:
--   The LEx2 construction uses the degree Of prod linear le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DegreeOfProdLinearLe.lean#L240-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DegreeOfProdLinearLe.lean#L240-L257

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open MvPolynomial

theorem Formalism.FourierDecayAlt.P.LEx2.degreeOf_prod_linear_le (N n : ℕ) (lam : Fin n → ℝ) (c : ℝ) (a : Fin N) :
    (C c * ∏ b : Fin N, ∏ s : Fin n, (X b + C (lam s)) : MvPolynomial (Fin N) ℝ).degreeOf a ≤ n := by sorry
