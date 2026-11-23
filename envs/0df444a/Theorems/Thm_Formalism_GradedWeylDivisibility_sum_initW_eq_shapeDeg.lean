-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_sum_initW_eq_shapeDeg
-- name    : Formalism.GradedWeylDivisibility.sum_initW_eq_shapeDeg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:37.466802+00:00
-- url     : https://prove2.me/theorems/a105a8e5-c5fb-4fb2-9ac2-ba2324d45ff9
-- title:
--   Graded Weyl Divisibility: sum init W eq shape Deg
-- statement:
--   The Graded Weyl Divisibility construction uses the sum init W eq shape Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/BideterminantMem.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/BideterminantMem.lean#L11-L15

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantMem
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

theorem Formalism.GradedWeylDivisibility.sum_initW_eq_shapeDeg {n K : ℕ} (sz : Fin K → ℕ) :
    (∑ k : Fin K, initW n (sz k)) = shapeDeg sz := by sorry
