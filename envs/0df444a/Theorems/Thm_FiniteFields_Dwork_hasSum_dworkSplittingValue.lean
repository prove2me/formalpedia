-- Prove2me | Theorems.Thm_FiniteFields_Dwork_hasSum_dworkSplittingValue
-- name    : FiniteFields.Dwork.hasSum_dworkSplittingValue
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T01:48:13.047984+00:00
-- url     : https://prove2.me/theorems/190e402a-d5ba-4006-857b-25c55f8a63bb
-- title:
--   Convergence of Dwork's splitting series $\theta$ at Teichmüller points
-- statement:
--   Let $p$ be a prime and $k$ a finite field of characteristic $p$, with $q=|k|=p^a$ elements, $a=[k:\mathbb F_p]$. Write $W(k)$ for the ring of $p$-typical Witt vectors of $k$, $F$ for its Witt vector Frobenius, $K$ for the completion of the fraction field of $W(k)$ with respect to its $p$-adic valuation, and $\sigma$ for the continuous extension of $F$ to $K$. Let $L=K(\zeta)$ be the $p$-th cyclotomic extension of $K$, where $\zeta\in L$ is a fixed primitive $p$-th root of unity, equipped with the spectral norm $|\cdot|$ extending the absolute value of $K$. For $x\in k$, write $\hat x\in L$ for the image of the Teichmüller representative $[x]\in W(k)$.
--
--   Let $\mathbb E(X)=\exp\big(-\sum_{j\ge0}X^{p^j}/p^j\big)$ be the (inverse) Artin–Hasse exponential, a power series with $p$-integral rational coefficients, and let $\eta\in L$ be the unique element with $|\eta|\le|\zeta-1|$, $|\eta|<1$ and $\mathbb E(\eta)=\zeta$. Dwork's splitting series is $\theta(X)=\mathbb E(\eta X)=\sum_{n\ge0}\beta_nX^n\in L[[X]]$, and for $x\in k$ the splitting value $\theta(\hat x)$ is the sum $\sum_{n\ge0}\beta_n\hat x^{\,n}$ in $L$.
--
--   Then for every $x\in k$ (including $x=0$), the series $\sum_{n\ge0}\beta_n\hat x^{\,n}$ converges in $L$ and its sum is the splitting value:
--   $$\sum_{n=0}^{\infty}\beta_n\,\hat x^{\,n}=\theta(\hat x).$$
--
--   The splitting values $\theta(\hat x)$ are the building blocks of Dwork's additive character, $\psi(x)=\prod_{i<a}\theta\big(\widehat{x^{p^i}}\big)$, and of the splitting product $H$ that defines the operator $\psi\circ H$.
--
--   **Formalization Note** The splitting value $\theta(\hat x)$ is defined as the unconditional sum `tsum`, which is $0$ by convention for a non-summable family; the content of the statement is that the family $(\beta_n\hat x^{\,n})_{n\ge0}$ is summable (`HasSum`), so that this definition is the genuine sum. The sign convention $\mathbb E(X)=\exp(-\sum_j X^{p^j}/p^j)$ is the one used in the formalization.
-- source:
--   B. Dwork, *On the rationality of the zeta function of an algebraic variety*, Amer. J. Math. 82 (1960), 631–648, §1, formulas (5)–(6) (the series $\theta(t)$ and the estimate $\operatorname{ord}\beta_m\ge m/(p-1)$), together with the remark on the Artin–Hasse exponential at the end of §1. Lean: ported from the `finite_fields` project (commit e8b5bf14), file `WeilConjectures/Dwork/AdditiveCharacter.lean`, declaration `WeilConjectures.Dwork.hasSum_dworkSplittingValue`

import Mathlib
import Definitions.Def_FiniteFields_Dwork_AdditiveCharacter

open scoped BigOperators WithZero
open FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [hpChar : CharP k p] [Finite k]
attribute [local instance] FiniteFields.Dwork.dw4eResiduePrimeAlgebra
attribute [local instance] FiniteFields.Dwork.dw4eDecidableEq

theorem FiniteFields.Dwork.hasSum_dworkSplittingValue (x : k) :
    HasSum
      (fun n : ℕ => PowerSeries.coeff n (dworkSplittingFunction k p) *
        ramifiedTeichmullerLift k p x ^ n)
      (dworkSplittingValue k p x) := by sorry
