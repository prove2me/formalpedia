-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_binomialSeries_sub_one
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.hasSubst_binomialSeries_sub_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:04:12.350135+00:00
-- url     : https://prove2.me/theorems/911a83e9-d334-4c7c-8b94-59adb3a9037c
-- title:
--   Height Descent Minors: has Subst binomial Series sub one
-- statement:
--   The Height Descent Minors construction uses the has Subst binomial Series sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L59-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L59-L63

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable {R : Type*} [CommRing R]
variable [BinomialRing R]

theorem Formalism.CohomologicalDescent.HeightDescentMinors.hasSubst_binomialSeries_sub_one {A : Type*} [CommRing A] [Algebra R A] (e : R) :
    HasSubst (binomialSeries A e - 1 : A⟦X⟧) := by sorry
