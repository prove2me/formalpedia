-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ldbasis_rowWt_bidetExp
-- name    : Formalism.GradedWeylDivisibility.ldbasis_rowWt_bidetExp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:02.845038+00:00
-- url     : https://prove2.me/theorems/be649b8f-198f-4bd7-b799-4c3051157fde
-- title:
--   Graded Weyl Divisibility: ldbasis row Wt bidet Exp
-- statement:
--   The Graded Weyl Divisibility construction uses the ldbasis row Wt bidet Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LDbasisLemmas.lean#L67-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LDbasisLemmas.lean#L67-L81

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

theorem Formalism.GradedWeylDivisibility.ldbasis_rowWt_bidetExp {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) :
    rowWt (bidetExp sz hsz I) = ∑ k : Fin K, ∑ p : Fin (sz k), (Pi.single (I k p) 1 : Fin r → ℕ) := by sorry
