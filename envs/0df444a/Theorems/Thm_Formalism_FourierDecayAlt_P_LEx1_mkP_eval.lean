-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_mkP_eval
-- name    : Formalism.FourierDecayAlt.P.LEx1.mkP_eval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:02:30.764805+00:00
-- url     : https://prove2.me/theorems/7e744b2c-bf2d-449c-a924-a9e183d5a76a
-- title:
--   LEx1: mk P eval
-- statement:
--   The LEx1 construction uses the mk P eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LemmaEprimeFromSteps.lean#L156-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LemmaEprimeFromSteps.lean#L156-L160

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

theorem Formalism.FourierDecayAlt.P.LEx1.mkP_eval (m : ℕ) (c : ℕ → ℂ) (z : ℂ) : (mkP m c).eval z = ∑ q ∈ range (m + 1), z ^ q * c q := by sorry
