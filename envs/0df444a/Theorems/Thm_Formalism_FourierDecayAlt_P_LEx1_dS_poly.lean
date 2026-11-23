-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_dS_poly
-- name    : Formalism.FourierDecayAlt.P.LEx1.dS_poly
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:51:48.536226+00:00
-- url     : https://prove2.me/theorems/cd92fa2a-7d28-4b89-9154-c19036a462c0
-- title:
--   LEx1: d S poly
-- statement:
--   The LEx1 construction uses the d S poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2ConstMul.lean#L137-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2ConstMul.lean#L137-L146

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2ConstMul
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

theorem Formalism.FourierDecayAlt.P.LEx1.dS_poly (B : Base) {A A' : Type} (T : Fn B A → Fn B A') (u : Fn B A) (d : ℕ) (c : ℕ → Fn B A')
    (hc : ∀ (s : ℝ) ω a, conjS B T u s ω a = ∑ q ∈ range (d + 1), (s : ℂ) ^ q * c q ω a) (p : ℕ) (ω : B.Ω) (a : A') :
    dS B T u p ω a = p.factorial * (if p < d + 1 then c p ω a else 0) := by sorry
