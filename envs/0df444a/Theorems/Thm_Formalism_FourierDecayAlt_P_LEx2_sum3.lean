-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_sum3
-- name    : Formalism.FourierDecayAlt.P.LEx2.sum3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:27.265329+00:00
-- url     : https://prove2.me/theorems/d78063ac-2ef5-40c7-ac4b-fe1ad4ab75e7
-- title:
--   LEx2: sum3
-- statement:
--   The LEx2 construction uses the sum3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2BoundedMul.lean#L621-L625
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2BoundedMul.lean#L621-L625

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasIterDeriv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
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

theorem Formalism.FourierDecayAlt.P.LEx2.sum3 {K K' : Type} [Fintype K] [Fintype K'] (n : ℕ) (f : K → K' → ℕ → ℂ) :
    ∑ k, ∑ κ, ∑ q ∈ range n, f k κ q = ∑ q ∈ range n, ∑ k, ∑ κ, f k κ q := by sorry
