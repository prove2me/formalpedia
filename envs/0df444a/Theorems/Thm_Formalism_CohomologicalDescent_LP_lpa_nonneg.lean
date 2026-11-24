-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LP_lpa_nonneg
-- name    : Formalism.CohomologicalDescent.LP.lpa_nonneg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:54:57.72014+00:00
-- url     : https://prove2.me/theorems/9aa2c1b1-4a6b-4192-a8b9-64b21b9273fa
-- title:
--   LP: lpa nonneg
-- statement:
--   The LP construction uses the lpa nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightDominantHolds.lean#L7-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightDominantHolds.lean#L7-L11

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLP
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightDominantHolds
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

theorem Formalism.CohomologicalDescent.LP.lpa_nonneg {K N : Type*} [Field K] [LinearOrder K] [AddCommGroup N] [Module K N] {q : ℕ}
    {T : Fin q → Fin q → Module.End K N} {B : LinearMap.BilinForm K N} (h : FormMod T B) (x : N) : 0 ≤ B x x := by sorry
