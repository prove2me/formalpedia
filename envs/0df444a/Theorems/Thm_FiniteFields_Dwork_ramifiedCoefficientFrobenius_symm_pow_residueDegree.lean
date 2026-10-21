-- Prove2me | Theorems.Thm_FiniteFields_Dwork_ramifiedCoefficientFrobenius_symm_pow_residueDegree
-- name    : FiniteFields.Dwork.ramifiedCoefficientFrobenius_symm_pow_residueDegree
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T01:43:59.048977+00:00
-- url     : https://prove2.me/theorems/3ce85dd9-67b8-451d-ae93-1c96666068d0
-- title:
--   The inverse Frobenius of $K(\zeta_p)$ has order dividing $a=[k:\mathbb F_p]$
-- statement:
--   Let $p$ be a prime and $k$ a finite field of characteristic $p$ with $q=p^a$ elements, $a=[k:\mathbb F_p]$. Let $K$ be the completed fraction field of the Witt vectors $W(k)$ and $\sigma\colon K\to K$ its Frobenius automorphism (the continuous extension of the Witt vector Frobenius). Let $L=K(\zeta)$ be the $p$-th cyclotomic extension of $K$, with $\zeta$ a fixed primitive $p$-th root of unity, and let $\tilde\sigma\colon L\to L$ be the ring automorphism which restricts to $\sigma$ on $K$ and fixes $\zeta$. Then for every $x\in L$,
--   $$\big(\tilde\sigma^{-1}\big)^{a}(x)=x .$$
--
--   In other words $\tilde\sigma^{a}$ is the identity of $L$. Consequently, the $a$-fold iterate of Dwork's $p$-level operator, which is only $\tilde\sigma^{-1}$-semilinear, is genuinely $L$-linear; this is how the $q$-level operator $\psi\circ H$ of §2 is obtained.
--
--   **Formalization Note** $\tilde\sigma$ is defined through the presentation of $L$ as $K[X]/(\Phi_p)$ by sending $X$ to the root $\zeta$; $a$ is `Module.finrank (ZMod p) k`, and $(\tilde\sigma^{-1})^{a}$ is the $a$-th iterate of the inverse ring equivalence.
-- source:
--   B. Dwork, *On the rationality of the zeta function of an algebraic variety*, Amer. J. Math. 82 (1960), 631–648, §1–§2 (the Frobenius $\sigma$ of the coefficient field, extended to $L(\zeta_p)$ with $\zeta_p$ fixed; passage from $p$ to $q=p^a$); auxiliary lemma in the formalization of §2, with no separately numbered counterpart in the paper. Lean: ported from the `finite_fields` project (commit e8b5bf14), file `WeilConjectures/Dwork/DworkNuclearOperator/CoefficientFrobenius.lean`, declaration `WeilConjectures.Dwork.ramifiedCoefficientFrobenius_symm_pow_residueDegree`

import Mathlib
import Definitions.Def_FiniteFields_Dwork_NuclearOperator

open Filter Topology
open FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
attribute [local instance] FiniteFields.Dwork.dw5bResiduePrimeAlgebra

theorem FiniteFields.Dwork.ramifiedCoefficientFrobenius_symm_pow_residueDegree (x : DworkCyclotomicField k p) :
    (ramifiedCoefficientFrobenius k p).symm^[Module.finrank (ZMod p) k] x = x := by sorry
