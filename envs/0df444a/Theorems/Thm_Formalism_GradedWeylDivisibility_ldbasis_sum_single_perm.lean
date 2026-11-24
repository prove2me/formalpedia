-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ldbasis_sum_single_perm
-- name    : Formalism.GradedWeylDivisibility.ldbasis_sum_single_perm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:49.606244+00:00
-- url     : https://prove2.me/theorems/08aa3286-2adc-4622-a3f0-927d71ea34e6
-- title:
--   Graded Weyl Divisibility: ldbasis sum single perm
-- statement:
--   The Graded Weyl Divisibility construction uses the ldbasis sum single perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LDbasisLemmas.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LDbasisLemmas.lean#L37-L39

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
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
open scoped MonomialOrder

theorem Formalism.GradedWeylDivisibility.ldbasis_sum_single_perm {r s : ℕ} (I : Fin s → Fin r) (σ : Equiv.Perm (Fin s)) :
    (∑ q : Fin s, (Pi.single (I (σ q)) 1 : Fin r → ℕ)) = ∑ p : Fin s, Pi.single (I p) 1 := by sorry
