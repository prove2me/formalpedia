-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_int_pr_self
-- name    : Formalism.FourierDecayAlt.P.LEx2.int_pr_self
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:04:07.085186+00:00
-- url     : https://prove2.me/theorems/58218193-3c8c-46a6-9e7c-e245c6768865
-- title:
--   LEx2: int pr self
-- statement:
--   The LEx2 construction uses the int pr self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThetaLimit.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThetaLimit.lean#L21-L23

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

theorem Formalism.FourierDecayAlt.P.LEx2.int_pr_self (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (v : Fn B A) :
    ∫ ω, pr B wt v v ω ∂B.μ = ((∫ ω, LE.sq B wt v ω ∂B.μ : ℝ) : ℂ) := by sorry
