-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_iterDeriv_poly
-- name    : Formalism.FourierDecayAlt.P.LEx2.iterDeriv_poly
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:04:22.808068+00:00
-- url     : https://prove2.me/theorems/8200666d-c3b9-4d7b-b5fc-e66056bbb7e1
-- title:
--   LEx2: iter Deriv poly
-- statement:
--   The LEx2 construction uses the iter Deriv poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThetaLimit.lean#L139-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThetaLimit.lean#L139-L149

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
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
open scoped ComplexConjugate
open Polynomial

theorem Formalism.FourierDecayAlt.P.LEx2.iterDeriv_poly (P : ℂ[X]) (p : ℕ) :
    iteratedDeriv p (fun s : ℝ => P.eval (s : ℂ)) = fun s : ℝ => ((derivative^[p]) P).eval (s : ℂ) := by sorry
