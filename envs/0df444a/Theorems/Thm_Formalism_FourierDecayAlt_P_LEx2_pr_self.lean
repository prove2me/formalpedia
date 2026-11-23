-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_pr_self
-- name    : Formalism.FourierDecayAlt.P.LEx2.pr_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:28.363064+00:00
-- url     : https://prove2.me/theorems/b9db358d-35bd-4d32-8c0b-3e2cac35fcc4
-- title:
--   LEx2: pr self
-- statement:
--   The LEx2 construction uses the pr self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThetaLimit.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThetaLimit.lean#L15-L19

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

theorem Formalism.FourierDecayAlt.P.LEx2.pr_self (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (v : Fn B A) (ω : B.Ω) :
    pr B wt v v ω = ((LE.sq B wt v ω : ℝ) : ℂ) := by sorry
