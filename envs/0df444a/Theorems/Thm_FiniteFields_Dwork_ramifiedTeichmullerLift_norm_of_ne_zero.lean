-- Prove2me | Theorems.Thm_FiniteFields_Dwork_ramifiedTeichmullerLift_norm_of_ne_zero
-- name    : FiniteFields.Dwork.ramifiedTeichmullerLift_norm_of_ne_zero
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T01:46:31.585718+00:00
-- url     : https://prove2.me/theorems/53382056-118e-48bf-b04b-e3fd7bc74035
-- title:
--   Teichmüller representatives of nonzero elements have norm $1$
-- statement:
--   Let $p$ be a prime and $k$ a finite field of characteristic $p$, with $q=|k|=p^a$ elements, $a=[k:\mathbb F_p]$. Write $W(k)$ for the ring of $p$-typical Witt vectors of $k$, $F$ for its Witt vector Frobenius, $K$ for the completion of the fraction field of $W(k)$ with respect to its $p$-adic valuation, and $\sigma$ for the continuous extension of $F$ to $K$. Let $L=K(\zeta)$ be the $p$-th cyclotomic extension of $K$, where $\zeta\in L$ is a fixed primitive $p$-th root of unity, equipped with the spectral norm $|\cdot|$ extending the absolute value of $K$. For $x\in k$, write $\hat x\in L$ for the image of the Teichmüller representative $[x]\in W(k)$.
--
--   Then for every nonzero $x\in k$,
--   $$|\hat x|=1 .$$
--
--   Thus the Teichmüller representative of a nonzero residue is a unit of the valuation ring of $L$ (indeed a $(q-1)$-st root of unity). This is the basic norm estimate behind the convergence of the splitting values $\theta(\hat x)$ and of Dwork's splitting product at Teichmüller points.
--
--   **Formalization Note** The norm on $L$ is the spectral norm of the finite extension $L/K$, where the norm of $K$ comes from its discrete valuation normalized by $v(p)=e^{-1}$; the statement does not depend on this normalization.
-- source:
--   B. Dwork, *On the rationality of the zeta function of an algebraic variety*, Amer. J. Math. 82 (1960), 631–648, §1 (Teichmüller representatives in the unramified field $L$); auxiliary lemma in the formalization of §1, with no separately numbered counterpart in the paper. Lean: ported from the `finite_fields` project (commit e8b5bf14), file `WeilConjectures/Dwork/AdditiveCharacter.lean`, declaration `WeilConjectures.Dwork.ramifiedTeichmullerLift_norm_of_ne_zero`

import Mathlib
import Definitions.Def_FiniteFields_Dwork_AdditiveCharacter

open scoped BigOperators WithZero
open FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [hpChar : CharP k p] [Finite k]
attribute [local instance] FiniteFields.Dwork.dw4eResiduePrimeAlgebra
attribute [local instance] FiniteFields.Dwork.dw4eDecidableEq

theorem FiniteFields.Dwork.ramifiedTeichmullerLift_norm_of_ne_zero {x : k} (hx : x ≠ 0) :
    ‖ramifiedTeichmullerLift k p x‖ = 1 := by sorry
