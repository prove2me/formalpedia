-- Prove2me | Theorems.Thm_FiniteFields_Dwork_norm_artinHasseEvalAt_eta_sub_one_le
-- name    : FiniteFields.Dwork.norm_artinHasseEvalAt_eta_sub_one_le
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T01:52:35.855832+00:00
-- url     : https://prove2.me/theorems/8b1245a3-27ca-422a-b573-d8300a91c99f
-- title:
--   Artin–Hasse values of Frobenius-fixed Witt vectors with $p$-adically small $D_0$ are close to $1$
-- statement:
--   Let $p$ be a prime and $k$ a finite field of characteristic $p$, with $q=|k|=p^a$ elements, $a=[k:\mathbb F_p]$. Write $W(k)$ for the ring of $p$-typical Witt vectors of $k$, $F$ for its Witt vector Frobenius, $K$ for the completion of the fraction field of $W(k)$ with respect to its $p$-adic valuation, and $\sigma$ for the continuous extension of $F$ to $K$. Let $L=K(\zeta)$ be the $p$-th cyclotomic extension of $K$, where $\zeta\in L$ is a fixed primitive $p$-th root of unity, equipped with the spectral norm $|\cdot|$ extending the absolute value of $K$. For $x\in k$, write $\hat x\in L$ for the image of the Teichmüller representative $[x]\in W(k)$.
--
--   Let $\mathbb E(X)=\exp\big(-\sum_{j\ge0}X^{p^j}/p^j\big)$ be the (inverse) Artin–Hasse exponential, a power series with $p$-integral rational coefficients, and let $\eta\in L$ be the unique element with $|\eta|\le|\zeta-1|$, $|\eta|<1$ and $\mathbb E(\eta)=\zeta$. Dwork's splitting series is $\theta(X)=\mathbb E(\eta X)=\sum_{n\ge0}\beta_nX^n\in L[[X]]$, and for $x\in k$ the splitting value $\theta(\hat x)$ is the sum $\sum_{n\ge0}\beta_n\hat x^{\,n}$ in $L$.
--
--   Let $W(W(k))$ be the ring of $p$-typical Witt vectors with coefficients in the ring $W(k)$, with Teichmüller map $r\mapsto[r]$ and Witt vector Frobenius $\mathbf F$ (the Frobenius of Witt vectors over the characteristic-zero ring $W(k)$, characterized by shifting ghost components). For $D=(D_0,D_1,\dots)\in W(W(k))$ define its Artin–Hasse series
--   $$\mathfrak E_D(X)=\prod_{i\ge0}\mathbb E\big(D_i\,X^{p^i}\big)\in W(k)[[X]],$$
--   a convergent product in the $X$-adic topology (here $\mathbb E$ has $p$-integral coefficients, so it makes sense over $W(k)$), and let $\mathfrak E_D(\eta)\in L$ be its value at $\eta$, obtained by mapping coefficients to $L$ and summing.
--
--   Let $D\in W(W(k))$ satisfy $\mathbf F(D)=D$, let $m\ge0$, and suppose that the zeroth component $D_0\in W(k)$, viewed in $L$, satisfies
--   $$|D_0|\le|p|^{2m+2}.$$
--   Then
--   $$\big|\mathfrak E_D(\eta)-1\big|\le|p|^{m}.$$
--
--   This convergence estimate is the analytic input in the proof of Dwork's formula (8): after subtracting from the trace vector an integer congruent to its trace modulo a high power of $p$, the remaining Frobenius-fixed vector has Artin–Hasse value arbitrarily close to $1$, which forces the product of splitting values to equal $\zeta^{\operatorname{Tr}(x)}$.
--
--   **Formalization Note** $\mathfrak E_D(\eta)$ is `artinHasseEvalAt k p D η`, the `tsum` evaluation of the coefficient-mapped Artin–Hasse series; $\mathbf F$ is Mathlib's `WittVector.frobenius` on $W(R)$ with $R=W(k)$, which is not the coefficientwise $p$-th power map since $R$ has characteristic zero. Norms are those of $L$, and $D_0$ is mapped to $L$ through $W(k)\to K\to L$.
-- source:
--   B. Dwork, *On the rationality of the zeta function of an algebraic variety*, Amer. J. Math. 82 (1960), 631–648, §1, formula (8) and the remark on the Artin–Hasse exponential $E(X)=\exp(\sum_j X^{p^j}/p^j)$ at the end of §1; auxiliary estimate in the formalization of (8), with no direct counterpart in the paper. Lean: ported from the `finite_fields` project (commit e8b5bf14), file `WeilConjectures/Dwork/WittTraceCharacter/TraceLimit.lean`, declaration `WeilConjectures.Dwork.norm_artinHasseEvalAt_eta_sub_one_le`

import Mathlib
import Definitions.Def_FiniteFields_Dwork_AdditiveCharacter

open PowerSeries IsUltrametricDist
open FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
attribute [local instance] FiniteFields.Dwork.dw4e2TraceLimitResiduePrimeAlgebra

theorem FiniteFields.Dwork.norm_artinHasseEvalAt_eta_sub_one_le (D : WittVector p (CoefficientRing k p))
    (hD : WittVector.frobenius D = D) (m : ℕ)
    (hD0 : ‖cyclotomicCoefficientMap k p (D.coeff 0)‖
      ≤ ‖(p : DworkCyclotomicField k p)‖ ^ (2 * m + 2)) :
    ‖artinHasseEvalAt k p D (dworkArtinHasseParameter k p) - 1‖
      ≤ ‖(p : DworkCyclotomicField k p)‖ ^ m := by sorry
