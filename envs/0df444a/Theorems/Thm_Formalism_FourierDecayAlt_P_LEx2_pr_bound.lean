-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_pr_bound
-- name    : Formalism.FourierDecayAlt.P.LEx2.pr_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T19:52:17.799807+00:00
-- url     : https://prove2.me/theorems/61a30bf9-61c1-493a-929e-aa666decac50
-- title:
--   LEx2: pr bound
-- statement:
--   The LEx2 construction uses the pr bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThetaLimit.lean#L521-L530
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThetaLimit.lean#L521-L530

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

theorem Formalism.FourierDecayAlt.P.LEx2.pr_bound (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (hpos : ∀ ω a, 0 ≤ wt ω a) (a b : Fn B A)
    (δ : ℝ) (hδ : 0 < δ) (ω : B.Ω) : ‖pr B wt a b ω‖ ≤ (LE.sq B wt a ω / δ + δ * LE.sq B wt b ω) / 2 := by sorry
