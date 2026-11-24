-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_rowNu_partial_sum
-- name    : Formalism.GradedWeylDivisibility.rowNu_partial_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:28.168749+00:00
-- url     : https://prove2.me/theorems/87907f9a-6d6b-4016-933e-5a4098a96cba
-- title:
--   Graded Weyl Divisibility: row Nu partial sum
-- statement:
--   The Graded Weyl Divisibility construction uses the row Nu partial sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DualWeylDominanceOf.lean#L21-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DualWeylDominanceOf.lean#L21-L39

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

theorem Formalism.GradedWeylDivisibility.rowNu_partial_sum {r n : ℕ} (ν : Fin n → ℕ) (hnr : n ≤ r) (k : ℕ) :
    (∑ a : Fin r with a.val < k, rowNu (r := r) ν a) = ∑ t : Fin n with t.val < k, ν t := by sorry
