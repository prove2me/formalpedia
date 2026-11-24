-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_sum_min_eq_shapeDeg
-- name    : Formalism.GradedWeylDivisibility.sum_min_eq_shapeDeg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:10.970694+00:00
-- url     : https://prove2.me/theorems/e76fbf7b-a528-4fb1-b0a5-1772d7cc58c3
-- title:
--   Graded Weyl Divisibility: sum min eq shape Deg
-- statement:
--   The Graded Weyl Divisibility construction uses the sum min eq shape Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetdomLemmas.lean#L169-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetdomLemmas.lean#L169-L182

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetdomLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.sum_min_eq_shapeDeg {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (k : ℕ) :
    ∑ k' : Fin K, min k (sz k') = ∑ t : Fin n with t.val < k, shapeDeg sz t := by sorry
