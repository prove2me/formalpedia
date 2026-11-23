-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_sq_comb_le
-- name    : Formalism.FourierDecayAlt.P.LEx1.sq_comb_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:19:12.972981+00:00
-- url     : https://prove2.me/theorems/772920ae-a5f7-4226-a4e7-0357909b098f
-- title:
--   LEx1: sq comb le
-- statement:
--   The LEx1 construction uses the sq comb le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LemmaEprimeFromSteps.lean#L407-L431
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LemmaEprimeFromSteps.lean#L407-L431

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

theorem Formalism.FourierDecayAlt.P.LEx1.sq_comb_le (B : Base) {A' : Type} [Fintype A'] (wt : B.Ω → A' → ℝ) (hpos : ∀ ω a, 0 ≤ wt ω a)
    (D : ℕ → Fn B A') (M : ℕ) (k : ℕ → B.Ω → ℝ) (K : ℝ) (hK : ∀ p ∈ range (M+1), ∀ ω, |k p ω| ≤ K) (ω : B.Ω) :
    LE.sq B wt (fun ω a => ∑ p ∈ range (M + 1), (k p ω : ℂ) * D p ω a / p.factorial) ω ≤
      (M + 1) * K ^ 2 * ∑ p ∈ range (M + 1), LE.sq B wt (D p) ω := by sorry
