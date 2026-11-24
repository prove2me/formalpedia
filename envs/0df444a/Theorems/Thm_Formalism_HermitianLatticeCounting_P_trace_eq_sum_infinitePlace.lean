-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_trace_eq_sum_infinitePlace
-- name    : Formalism.HermitianLatticeCounting.P.trace_eq_sum_infinitePlace
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:32.996926+00:00
-- url     : https://prove2.me/theorems/7348768a-6bc3-49df-a095-0959177ab09a
-- title:
--   P: trace eq sum infinite Place
-- statement:
--   The P construction uses the trace eq sum infinite Place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SumComplexEmbeddingsEqSumInfinitePlace.lean#L37-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SumComplexEmbeddingsEqSumInfinitePlace.lean#L37-L55

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

theorem Formalism.HermitianLatticeCounting.P.trace_eq_sum_infinitePlace {E : Type} [Field E] [NumberField E]
    (hc : ∀ w : InfinitePlace E, w.IsComplex) (a : E) :
    ((Algebra.trace ℚ E a : ℚ) : ℝ) = ∑ w : InfinitePlace E, 2 * (w.embedding a).re := by sorry
