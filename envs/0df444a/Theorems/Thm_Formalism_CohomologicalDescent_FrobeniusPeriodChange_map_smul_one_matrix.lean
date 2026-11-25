-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_map_smul_one_matrix
-- name    : Formalism.CohomologicalDescent.FrobeniusPeriodChange.map_smul_one_matrix
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:21:27.92111+00:00
-- url     : https://prove2.me/theorems/978ec520-fea5-4f30-ba1b-e333415d438a
-- title:
--   Frobenius Period Change: map smul one matrix
-- statement:
--   The Frobenius Period Change construction uses the map smul one matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L301-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L301-L304

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

theorem Formalism.CohomologicalDescent.FrobeniusPeriodChange.map_smul_one_matrix {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) (x : R) :
    ((x • (1 : Matrix (Fin n) (Fin n) R))).map f = f x • (1 : Matrix (Fin n) (Fin n) S) := by sorry
