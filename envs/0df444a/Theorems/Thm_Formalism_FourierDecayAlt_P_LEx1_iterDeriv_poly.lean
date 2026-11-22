-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_iterDeriv_poly
-- name    : Formalism.FourierDecayAlt.P.LEx1.iterDeriv_poly
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:02:14.808798+00:00
-- url     : https://prove2.me/theorems/ec8a55b2-b8e2-4493-a3fe-b7bf7b68916f
-- title:
--   LEx1: iter Deriv poly
-- statement:
--   The LEx1 construction uses the iter Deriv poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LemmaEprimeFromSteps.lean#L140-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LemmaEprimeFromSteps.lean#L140-L150

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
open Polynomial

theorem Formalism.FourierDecayAlt.P.LEx1.iterDeriv_poly (P : ℂ[X]) (p : ℕ) :
    iteratedDeriv p (fun s : ℝ => P.eval (s : ℂ)) = fun s : ℝ => ((derivative^[p]) P).eval (s : ℂ) := by sorry
