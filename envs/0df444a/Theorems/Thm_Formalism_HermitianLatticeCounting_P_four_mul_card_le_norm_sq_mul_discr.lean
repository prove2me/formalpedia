-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_four_mul_card_le_norm_sq_mul_discr
-- name    : Formalism.HermitianLatticeCounting.P.four_mul_card_le_norm_sq_mul_discr
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:03:21.390322+00:00
-- url     : https://prove2.me/theorems/280ac880-bcaa-407f-9c6b-9e43fb8f889a
-- title:
--   P: four mul card le norm sq mul discr
-- statement:
--   The P construction uses the four mul card le norm sq mul discr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SumComplexEmbeddingsEqSumInfinitePlace.lean#L240-L371
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SumComplexEmbeddingsEqSumInfinitePlace.lean#L240-L371

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

theorem Formalism.HermitianLatticeCounting.P.four_mul_card_le_norm_sq_mul_discr (hc : ∀ w : InfinitePlace E, w.IsComplex) (y : s5bV E) (hy : y ≠ 0)
    (hint : ∀ x ∈ integerEmbeddingLattice hc, ∃ n : ℤ, inner ℝ x y = (n : ℝ)) :
    4 * (Fintype.card (InfinitePlace E) : ℝ) ≤
      ‖y‖ ^ 2 * |(discr E : ℝ)| ^ (1 / (Fintype.card (InfinitePlace E) : ℝ)) := by sorry
