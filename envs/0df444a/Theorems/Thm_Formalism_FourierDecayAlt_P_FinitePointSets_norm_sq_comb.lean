-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FinitePointSets_norm_sq_comb
-- name    : Formalism.FourierDecayAlt.P.FinitePointSets.norm_sq_comb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:24.03526+00:00
-- url     : https://prove2.me/theorems/b07a17df-e50c-443c-9fd2-1d90617a9134
-- title:
--   Finite Point Sets: norm sq comb
-- statement:
--   The Finite Point Sets construction uses the norm sq comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinitePointSets.lean#L77-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinitePointSets.lean#L77-L89

import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FinitePointSets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FinitePointSets
open Formalism.FourierDecayAlt.TB Finset Filter Topology
open scoped ComplexInnerProductSpace ComplexConjugate

theorem Formalism.FourierDecayAlt.P.FinitePointSets.norm_sq_comb {α H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Y : Finset α) (c : α → ℂ) (V : α → H) :
    ((‖∑ p ∈ Y, c p • V p‖ ^ 2 : ℝ) : ℂ)
      = ∑ p ∈ Y, ∑ q ∈ Y, (c p * conj (c q)) * ⟪V q, V p⟫ := by sorry
