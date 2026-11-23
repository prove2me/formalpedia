-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_meas_pr
-- name    : Formalism.FourierDecayAlt.P.LEx2.meas_pr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:53:46.531058+00:00
-- url     : https://prove2.me/theorems/5c985d2a-4cfb-413e-a846-3f88116ac7c3
-- title:
--   LEx2: meas pr
-- statement:
--   The LEx2 construction uses the meas pr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThetaLimit.lean#L532-L537
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThetaLimit.lean#L532-L537

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

theorem Formalism.FourierDecayAlt.P.LEx2.meas_pr (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (a b : Fn B A)
    (h0 : ∀ i, Measurable fun ω => wt ω i) (h1 : ∀ i, Measurable fun ω => a ω i) (h2 : ∀ i, Measurable fun ω => b ω i) :
    Measurable (pr B wt a b) := by sorry
