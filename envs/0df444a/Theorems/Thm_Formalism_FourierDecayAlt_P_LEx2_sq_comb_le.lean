-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_sq_comb_le
-- name    : Formalism.FourierDecayAlt.P.LEx2.sq_comb_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:29.712804+00:00
-- url     : https://prove2.me/theorems/c4564c4f-252d-432c-ae3b-531791b89058
-- title:
--   LEx2: sq comb le
-- statement:
--   The LEx2 construction uses the sq comb le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThetaLimit.lean#L406-L430
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThetaLimit.lean#L406-L430

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

theorem Formalism.FourierDecayAlt.P.LEx2.sq_comb_le (B : Base) {A' : Type} [Fintype A'] (wt : B.Ω → A' → ℝ) (hpos : ∀ ω a, 0 ≤ wt ω a)
    (D : ℕ → Fn B A') (M : ℕ) (k : ℕ → B.Ω → ℝ) (K : ℝ) (hK : ∀ p ∈ range (M+1), ∀ ω, |k p ω| ≤ K) (ω : B.Ω) :
    LE.sq B wt (fun ω a => ∑ p ∈ range (M + 1), (k p ω : ℂ) * D p ω a / p.factorial) ω ≤
      (M + 1) * K ^ 2 * ∑ p ∈ range (M + 1), LE.sq B wt (D p) ω := by sorry
