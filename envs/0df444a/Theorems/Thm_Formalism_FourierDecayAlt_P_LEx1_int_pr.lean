-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_int_pr
-- name    : Formalism.FourierDecayAlt.P.LEx1.int_pr
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:02:10.981595+00:00
-- url     : https://prove2.me/theorems/6ecfebfa-e1fe-4d7a-abfd-3a796e09cac1
-- title:
--   LEx1: int pr
-- statement:
--   The LEx1 construction uses the int pr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LemmaEprimeFromSteps.lean#L540-L545
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LemmaEprimeFromSteps.lean#L540-L545

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

theorem Formalism.FourierDecayAlt.P.LEx1.int_pr (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (hpos : ∀ ω a, 0 ≤ wt ω a) (a b : Fn B A)
    (h0 : ∀ i, Measurable fun ω => wt ω i) (h1 : ∀ i, Measurable fun ω => a ω i) (h2 : ∀ i, Measurable fun ω => b ω i)
    (ha : Integrable (LE.sq B wt a) B.μ) (hb : Integrable (LE.sq B wt b) B.μ) : Integrable (pr B wt a b) B.μ := by sorry
