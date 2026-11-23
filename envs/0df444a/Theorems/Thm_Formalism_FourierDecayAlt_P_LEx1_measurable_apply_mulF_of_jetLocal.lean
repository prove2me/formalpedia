-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_measurable_apply_mulF_of_jetLocal
-- name    : Formalism.FourierDecayAlt.P.LEx1.measurable_apply_mulF_of_jetLocal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:53:11.91672+00:00
-- url     : https://prove2.me/theorems/aca59d81-11c9-44ba-93d3-ad9ce1cf8f8a
-- title:
--   LEx1: measurable apply mul F of jet Local
-- statement:
--   The LEx1 construction uses the measurable apply mul F of jet Local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LemmaEprimeFromSteps.lean#L36-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LemmaEprimeFromSteps.lean#L36-L43

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

theorem Formalism.FourierDecayAlt.P.LEx1.measurable_apply_mulF_of_jetLocal (hLeib : Leibniz) (B : Base) {A A' : Type} (T : Fn B A → Fn B A') (u : Fn B A) (M : ℕ)
    (hJ : JetLocal B T u) (hP : PolyS B T u M) (hm : ∀ p a, Measurable fun ω => dS B T u p ω a)
    (φ : ℝ → ℝ) (hφ : SmoothLog φ) (a : A') : Measurable fun ω => T (mulF B φ u) ω a := by sorry
