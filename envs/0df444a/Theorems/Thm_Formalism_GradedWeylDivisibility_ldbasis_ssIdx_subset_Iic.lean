-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ldbasis_ssIdx_subset_Iic
-- name    : Formalism.GradedWeylDivisibility.ldbasis_ssIdx_subset_Iic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:57.141014+00:00
-- url     : https://prove2.me/theorems/fa0a9e7f-10c4-40cc-a537-023ff4ab931c
-- title:
--   Graded Weyl Divisibility: ldbasis ss Idx subset Iic
-- statement:
--   The Graded Weyl Divisibility construction uses the ldbasis ss Idx subset Iic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/SSIdxFinite.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/SSIdxFinite.lean#L7-L16

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SSIdxFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.ldbasis_ssIdx_subset_Iic (k n : ℕ) (ν : Fin n → ℕ) :
    ssIdx k n ν ⊆ Set.Iic (Finsupp.equivFunOnFinite.symm (fun v : Fin k × Fin n => ν v.2)) := by sorry
