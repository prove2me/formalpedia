-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5bLat_mem
-- name    : Formalism.HermitianLatticeCounting.P.s5bLat_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:29:53.534452+00:00
-- url     : https://prove2.me/theorems/ccd6aecb-705e-4010-a593-01140fbe7b4b
-- title:
--   P: s5b Lat mem
-- statement:
--   The P construction uses the s5b Lat mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SumComplexEmbeddingsEqSumInfinitePlace.lean#L200-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SumComplexEmbeddingsEqSumInfinitePlace.lean#L200-L222

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
variable {E : Type} [Field E] [NumberField E]

theorem Formalism.HermitianLatticeCounting.P.s5bLat_mem (hc : ∀ w : InfinitePlace E, w.IsComplex) (x : s5bV E) :
    x ∈ integerEmbeddingLattice hc ↔ ∃ a : 𝓞 E, x = complexEmbeddingVector (a : E) := by sorry
