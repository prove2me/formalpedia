-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LP_lowW_all
-- name    : Formalism.CohomologicalDescent.LP.lowW_all
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:55:50.491216+00:00
-- url     : https://prove2.me/theorems/a4e27491-2c6a-42ed-9f1e-fa380e72188d
-- title:
--   LP: low W all
-- statement:
--   The LP construction uses the low W all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/GeneratedHighestWeightHolds.lean#L28-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/GeneratedHighestWeightHolds.lean#L28-L53

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

theorem Formalism.CohomologicalDescent.LP.lowW_all (T : Fin q → Fin q → Module.End K N) (hT : GlRel T) (κ : Fin q → K) (x : N) (hx : LowW T κ x) :
    ∀ a b, T a b x ∈ lowSpan T κ := by sorry
