-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LP_lowSpan_low
-- name    : Formalism.CohomologicalDescent.LP.lowSpan_low
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:54:48.902856+00:00
-- url     : https://prove2.me/theorems/e896db1c-c73c-49af-8160-aab58b8bfcc7
-- title:
--   LP: low Span low
-- statement:
--   The LP construction uses the low Span low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/GeneratedHighestWeightHolds.lean#L18-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/GeneratedHighestWeightHolds.lean#L18-L26

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLP
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_GeneratedHighestWeightHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LP
open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample
variable {K N : Type*} [CommRing K] [AddCommGroup N] [Module K N] {q : ℕ}

theorem Formalism.CohomologicalDescent.LP.lowSpan_low (T : Fin q → Fin q → Module.End K N) (κ : Fin q → K) (c d : Fin q) (h : d < c) :
    ∀ y ∈ lowSpan T κ, T c d y ∈ lowSpan T κ := by sorry
