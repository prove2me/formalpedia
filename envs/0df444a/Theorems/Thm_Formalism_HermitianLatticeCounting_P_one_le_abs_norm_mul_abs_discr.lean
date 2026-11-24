-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_one_le_abs_norm_mul_abs_discr
-- name    : Formalism.HermitianLatticeCounting.P.one_le_abs_norm_mul_abs_discr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:25.17951+00:00
-- url     : https://prove2.me/theorems/07d9f879-77ae-4e27-bf48-07d292305c1c
-- title:
--   P: one le abs norm mul abs discr
-- statement:
--   The P construction uses the one le abs norm mul abs discr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SumComplexEmbeddingsEqSumInfinitePlace.lean#L57-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SumComplexEmbeddingsEqSumInfinitePlace.lean#L57-L151

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

theorem Formalism.HermitianLatticeCounting.P.one_le_abs_norm_mul_abs_discr {E : Type} [Field E] [NumberField E] (z : E) (hz : z ≠ 0)
    (hint : ∀ a : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (z * (a : E)) = m) :
    1 ≤ |(Algebra.norm ℚ z : ℚ)| * |(NumberField.discr E : ℚ)| := by sorry
