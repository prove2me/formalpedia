-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_sum_fin_filter_lt_eq_range
-- name    : Formalism.GradedWeylDivisibility.sum_fin_filter_lt_eq_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:01.441178+00:00
-- url     : https://prove2.me/theorems/cb65d96b-f7be-4b36-9e4f-e09f41de2534
-- title:
--   Graded Weyl Divisibility: sum fin filter lt eq range
-- statement:
--   The Graded Weyl Divisibility construction uses the sum fin filter lt eq range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DualWeylDominanceOf.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DualWeylDominanceOf.lean#L10-L19

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantDominance
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylDominanceOf
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

theorem Formalism.GradedWeylDivisibility.sum_fin_filter_lt_eq_range {N : ℕ} (G : ℕ → ℕ) (k : ℕ) :
    ∑ a : Fin N with a.val < k, G a.val = ∑ i ∈ Finset.range (min N k), G i := by sorry
