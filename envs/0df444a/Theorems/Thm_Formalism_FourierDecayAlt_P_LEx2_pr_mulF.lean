-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_pr_mulF
-- name    : Formalism.FourierDecayAlt.P.LEx2.pr_mulF
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:33.044356+00:00
-- url     : https://prove2.me/theorems/72cd9859-6883-499d-a92c-daa00c74fc48
-- title:
--   LEx2: pr mul F
-- statement:
--   The LEx2 construction uses the pr mul F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThetaLimit.lean#L251-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThetaLimit.lean#L251-L255

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

theorem Formalism.FourierDecayAlt.P.LEx2.pr_mulF (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (h u : Fn B A) (φ : ℝ → ℝ) (ω : B.Ω) :
    pr B wt h (mulF B φ u) ω = (φ (B.G ω) : ℂ) * pr B wt h u ω := by sorry
