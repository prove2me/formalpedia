-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lccomp_pairW_col
-- name    : Formalism.GradedWeylDivisibility.lccomp_pairW_col
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:59.265975+00:00
-- url     : https://prove2.me/theorems/58f56d29-7573-4bef-b275-51940be18e78
-- title:
--   Graded Weyl Divisibility: lccomp pair W col
-- statement:
--   The Graded Weyl Divisibility construction uses the lccomp pair W col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCcompLemmas.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCcompLemmas.lean#L14-L17

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCcompLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.lccomp_pairW_col {r n : ℕ} (l j : Fin n) (b : Fin r) :
    pairW (r := r) l j (b, l) = Finsupp.single (b, l) 1 := by sorry
