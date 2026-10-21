-- Prove2me | Theorems.Thm_FiniteFields_Dwork_dworkSplittingValue_frobeniusProduct
-- name    : FiniteFields.Dwork.dworkSplittingValue_frobeniusProduct
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T01:50:29.479339+00:00
-- url     : https://prove2.me/theorems/8ca6a253-73b5-4aa7-a655-b2f14c6d5600
-- title:
--   Dwork's product of Frobenius-conjugate splitting values as an Artin–Hasse value
-- statement:
--   Let $p$ be a prime and $k$ a finite field of characteristic $p$, with $q=|k|=p^a$ elements, $a=[k:\mathbb F_p]$. Write $W(k)$ for the ring of $p$-typical Witt vectors of $k$, $F$ for its Witt vector Frobenius, $K$ for the completion of the fraction field of $W(k)$ with respect to its $p$-adic valuation, and $\sigma$ for the continuous extension of $F$ to $K$. Let $L=K(\zeta)$ be the $p$-th cyclotomic extension of $K$, where $\zeta\in L$ is a fixed primitive $p$-th root of unity, equipped with the spectral norm $|\cdot|$ extending the absolute value of $K$. For $x\in k$, write $\hat x\in L$ for the image of the Teichmüller representative $[x]\in W(k)$.
--
--   Let $\mathbb E(X)=\exp\big(-\sum_{j\ge0}X^{p^j}/p^j\big)$ be the (inverse) Artin–Hasse exponential, a power series with $p$-integral rational coefficients, and let $\eta\in L$ be the unique element with $|\eta|\le|\zeta-1|$, $|\eta|<1$ and $\mathbb E(\eta)=\zeta$. Dwork's splitting series is $\theta(X)=\mathbb E(\eta X)=\sum_{n\ge0}\beta_nX^n\in L[[X]]$, and for $x\in k$ the splitting value $\theta(\hat x)$ is the sum $\sum_{n\ge0}\beta_n\hat x^{\,n}$ in $L$.
--
--   Let $W(W(k))$ be the ring of $p$-typical Witt vectors with coefficients in the ring $W(k)$, with Teichmüller map $r\mapsto[r]$ and Witt vector Frobenius $\mathbf F$ (the Frobenius of Witt vectors over the characteristic-zero ring $W(k)$, characterized by shifting ghost components). For $D=(D_0,D_1,\dots)\in W(W(k))$ define its Artin–Hasse series
--   $$\mathfrak E_D(X)=\prod_{i\ge0}\mathbb E\big(D_i\,X^{p^i}\big)\in W(k)[[X]],$$
--   a convergent product in the $X$-adic topology (here $\mathbb E$ has $p$-integral coefficients, so it makes sense over $W(k)$), and let $\mathfrak E_D(\eta)\in L$ be its value at $\eta$, obtained by mapping coefficients to $L$ and summing.
--
--   For $x\in k$ consider the Witt vector
--   $$\tau(x)=\sum_{i=0}^{a-1}\big[F^{i}([x])\big]\in W(W(k)),$$
--   the sum (in the ring $W(W(k))$) of the Teichmüller vectors of the Frobenius conjugates $F^i([x])\in W(k)$ of the Teichmüller representative $[x]\in W(k)$. Then
--   $$\mathfrak E_{\tau(x)}(\eta)=\prod_{i=0}^{a-1}\theta\Big(\widehat{x^{p^i}}\Big).$$
--
--   The right-hand side is Dwork's product of splitting values over the Frobenius conjugates of $x$ (formula (7)). The identity rewrites it as the Artin–Hasse value of a single Witt vector whose zeroth component is the Witt-vector trace of $[x]$; this is the step from which Dwork's formula (8), $\prod_{i<a}\theta\big(\widehat{x^{p^i}}\big)=\zeta^{\operatorname{Tr}_{k/\mathbb F_p}(x)}$, is derived.
--
--   **Formalization Note** $\mathfrak E_D(\eta)$ is the value of the additive-to-multiplicative homomorphism `artinHasseWittHom` from $W(W(k))$ to the group of principal units $\{u\in L:|u-1|<1\}$; the statement reads off its underlying element of $L$. Teichmüller representatives commute with Frobenius, $F^i([x])=[x^{p^i}]$, which is how the factors on the right are indexed.
-- source:
--   B. Dwork, *On the rationality of the zeta function of an algebraic variety*, Amer. J. Math. 82 (1960), 631–648, §1, formula (7) (the product $\prod_{i<a}\theta(t^{p^i})$ over Frobenius conjugates), in the Witt-vector formulation suggested by the remark on the Artin–Hasse exponential at the end of §1. Lean: ported from the `finite_fields` project (commit e8b5bf14), file `WeilConjectures/Dwork/WittTraceCharacter/Specialization.lean`, declaration `WeilConjectures.Dwork.dworkSplittingValue_frobeniusProduct`

import Mathlib
import Definitions.Def_FiniteFields_Dwork_AdditiveCharacter

open PowerSeries IsUltrametricDist
open FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]

theorem FiniteFields.Dwork.dworkSplittingValue_frobeniusProduct (x : k) :
    (Additive.toMul (artinHasseWittHom k p
        (wittTraceTeichmuller k p (teichmullerLift k p x)))).val
      = dworkFrobeniusConjugateProduct k p x := by sorry
