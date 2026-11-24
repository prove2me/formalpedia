-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_toSquareBlock_mul_of_blockTriangular_alt
-- name    : Formalism.CohomologicalDescent.FrobeniusPeriodChange.toSquareBlock_mul_of_blockTriangular_alt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:53:48.156803+00:00
-- url     : https://prove2.me/theorems/c9d62971-08f5-4625-a2e4-944538073f7f
-- title:
--   Frobenius Period Change: to Square Block mul of block Triangular alt
-- statement:
--   The Frobenius Period Change construction uses the to Square Block mul of block Triangular alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L332-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L332-L345

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors

theorem Formalism.CohomologicalDescent.FrobeniusPeriodChange.toSquareBlock_mul_of_blockTriangular_alt {R : Type} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R)
    (b : Fin n → ℕ) (hA : A.BlockTriangular b) (hB : B.BlockTriangular b) (r : ℕ) :
    (A * B).toSquareBlock b r = A.toSquareBlock b r * B.toSquareBlock b r := by sorry
