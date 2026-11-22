-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ldiag_sum_filter_lt_eq_range
-- name    : Formalism.GradedWeylDivisibility.ldiag_sum_filter_lt_eq_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:22:38.024319+00:00
-- url     : https://prove2.me/theorems/d4510db1-0ff6-4b3b-9210-db21444a242d
-- title:
--   Graded Weyl Divisibility: ldiag sum filter lt eq range
-- statement:
--   The Graded Weyl Divisibility construction uses the ldiag sum filter lt eq range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DomPow.lean#L66-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DomPow.lean#L66-L79

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DomPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.ldiag_sum_filter_lt_eq_range {r : ℕ} (f : Fin r → ℕ) (k : ℕ) (hk : k ≤ r) :
    ∑ a : Fin r with a.val < k, f a = ∑ a ∈ range k, ldiagExt f a := by sorry
