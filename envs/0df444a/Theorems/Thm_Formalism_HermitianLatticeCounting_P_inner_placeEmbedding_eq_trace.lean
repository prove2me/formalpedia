-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_inner_placeEmbedding_eq_trace
-- name    : Formalism.HermitianLatticeCounting.P.inner_placeEmbedding_eq_trace
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:20.228802+00:00
-- url     : https://prove2.me/theorems/4f2716b7-faa0-40ba-8a94-ea22ce17ba1f
-- title:
--   P: inner place Embedding eq trace
-- statement:
--   The P construction uses the inner place Embedding eq trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SumComplexEmbeddingsEqSumInfinitePlace.lean#L232-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SumComplexEmbeddingsEqSumInfinitePlace.lean#L232-L238

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SumComplexEmbeddingsEqSumInfinitePlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open NumberField
open NumberField
open NumberField
variable {E : Type} [Field E] [NumberField E]

theorem Formalism.HermitianLatticeCounting.P.inner_placeEmbedding_eq_trace (hc : ∀ w : InfinitePlace E, w.IsComplex) (a z : E) :
    inner ℝ (complexEmbeddingVector a) (WithLp.toLp 2 (fun w : InfinitePlace E => 2 * conj (w.embedding z)) : s5bV E) =
      ((Algebra.trace ℚ E (z * a) : ℚ) : ℝ) := by sorry
