-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_pr_mulF
-- name    : Formalism.FourierDecayAlt.P.LEx1.pr_mulF
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:19:09.228988+00:00
-- url     : https://prove2.me/theorems/d6df0eb3-2c74-4774-b15c-cde87ab77f7a
-- title:
--   LEx1: pr mul F
-- statement:
--   The LEx1 construction uses the pr mul F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LemmaEprimeFromSteps.lean#L252-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LemmaEprimeFromSteps.lean#L252-L256

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

theorem Formalism.FourierDecayAlt.P.LEx1.pr_mulF (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (h u : Fn B A) (φ : ℝ → ℝ) (ω : B.Ω) :
    pr B wt h (mulF B φ u) ω = (φ (B.G ω) : ℂ) * pr B wt h u ω := by sorry
