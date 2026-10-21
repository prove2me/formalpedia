-- Prove2me | Theorems.Thm_FiniteFields_Dwork_tracePower_dworkQFrobeniusNuclearOperator_tendsto
-- name    : FiniteFields.Dwork.tracePower_dworkQFrobeniusNuclearOperator_tendsto
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T01:44:20.737812+00:00
-- url     : https://prove2.me/theorems/d71b82f7-773a-4075-8d25-6c1446120572
-- title:
--   Nuclear traces of powers of Dwork's $q$-level operator are limits of finite cutoff traces
-- statement:
--   Let $p$ be a prime and $k$ a finite field of characteristic $p$, with $q=|k|=p^a$ elements, $a=[k:\mathbb F_p]$. Write $W(k)$ for the ring of $p$-typical Witt vectors of $k$, $F$ for its Witt vector Frobenius, $K$ for the completion of the fraction field of $W(k)$ with respect to its $p$-adic valuation, and $\sigma$ for the continuous extension of $F$ to $K$. Let $L=K(\zeta)$ be the $p$-th cyclotomic extension of $K$, where $\zeta\in L$ is a fixed primitive $p$-th root of unity, equipped with the spectral norm $|\cdot|$ extending the absolute value of $K$. For $x\in k$, write $\hat x\in L$ for the image of the Teichmüller representative $[x]\in W(k)$.
--
--   Let $\mathbb E(X)=\exp\big(-\sum_{j\ge0}X^{p^j}/p^j\big)$ be the (inverse) Artin–Hasse exponential, a power series with $p$-integral rational coefficients, and let $\eta\in L$ be the unique element with $|\eta|\le|\zeta-1|$, $|\eta|<1$ and $\mathbb E(\eta)=\zeta$. Dwork's splitting series is $\theta(X)=\mathbb E(\eta X)=\sum_{n\ge0}\beta_nX^n\in L[[X]]$, and for $x\in k$ the splitting value $\theta(\hat x)$ is the sum $\sum_{n\ge0}\beta_n\hat x^{\,n}$ in $L$.
--
--   Fix $d\ge0$, a polynomial $f=\sum_u f_u x^u\in k[x_1,\dots,x_d]$ (monomials $x^u$, $u\in\mathbb N^d$), and a weight vector $w=(w_1,\dots,w_d)$ of positive integers; the weight of $u$ is $|u|_w=\sum_i w_iu_i$, and for $N\ge0$ the cutoff $M_N=\{u\in\mathbb N^d:|u|_w\le N\}$ is finite. On the Banach algebra of series $g=\sum_u c_ux^u$ with coefficients $c_u\in L$ tending to $0$, consider:
--
--   1. Dwork's splitting product $H(x)=\prod_{u:\,f_u\ne0}\theta\big(\hat f_u\,x^u\big)$;
--   2. the operator $\psi_p\big(\sum_u c_ux^u\big)=\sum_u c_{pu}x^u$;
--   3. the $p$-level Dwork operator $\alpha(g)=\tilde\sigma^{-1}\big(\psi_p(H\cdot g)\big)$, where $\tilde\sigma$ is the Frobenius of $L$ extending $\sigma$ and fixing $\zeta$, applied coefficientwise, and the $q$-level operator $\alpha_q=\alpha^{a}$ ($a$-fold iterate).
--
--   Let $A(u,v)$ be the coefficient of $x^u$ in $\alpha_q(x^v)$, and let $A_N=\big(A(u,v)\big)_{u,v\in M_N}$ be the finite cutoff matrix. Let $T$ be the nuclear operator attached to $\alpha_q$: its kernel is the diagonally conjugated matrix $\tilde A(u,v)=\gamma^{e(v)}\gamma^{-e(u)}A(u,v)$, where $\gamma=\zeta-1$ and $e(u)\in\mathbb N$ is an explicit exponent depending on $f$, $w$, $p$ and $|u|_w$, and for $s\ge1$ the trace of its $s$-th power is
--   $$\operatorname{Tr}(T^s)=\lim_{N\to\infty}\operatorname{tr}\big(\tilde A_N^{\,s}\big).$$
--   Then for every integer $s\ge1$, the finite traces of the unconjugated cutoff matrices converge to this nuclear trace:
--   $$\lim_{N\to\infty}\operatorname{tr}\big(A_N^{\,s}\big)=\operatorname{Tr}(T^s).$$
--
--   This lets the trace formula and the Fredholm determinant computations of §2–§3 work directly with the literal matrix coefficients of $\alpha_q=\psi\circ H$, while the nuclear decay estimates are carried by the normalized kernel.
--
--   **Formalization Note** $\operatorname{Tr}(T^s)$ is defined with Lean's `limUnder`, so the theorem asserts in particular that the limit on the left exists. The polynomial $f$ is given as a finitely supported coefficient function on $\mathbb N^d$, all monomials $u\in\mathbb N^d$ (including those with zero exponents) index the matrix, and $s$ ranges over positive integers (`ℕ+`). The exponent $e(u)$ is `dworkQDiagonalExponent`, $\lfloor(3p|u|_w-G)/(2G)\rfloor$ with truncated subtraction, where $G$ is an explicit positive integer depending on $f$, $w$ and $q$.
-- source:
--   B. Dwork, *On the rationality of the zeta function of an algebraic variety*, Amer. J. Math. 82 (1960), 631–648, §2 (the operator $\psi\circ H$, its matrix and the traces of its powers, Lemma 2 and formula (14)) and §3 (16)–(21) (Fredholm determinants as limits over finite cutoffs); auxiliary lemma in the formalization, with no direct counterpart in the paper, where traces are defined directly as sums of diagonal entries. Lean: ported from the `finite_fields` project (commit e8b5bf14), file `WeilConjectures/Dwork/DworkNuclearOperator/TracePowers.lean`, declaration `WeilConjectures.Dwork.tracePower_dworkQFrobeniusNuclearOperator_tendsto`

import Mathlib
import Definitions.Def_FiniteFields_Dwork_NuclearOperator

open Filter Topology
open FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
variable {d : ℕ} (w : PositiveMonomialWeight d)

theorem FiniteFields.Dwork.tracePower_dworkQFrobeniusNuclearOperator_tendsto (f : MonomialIndex d →₀ k)
    (power : ℕ+) :
    Tendsto (fun bound =>
        finiteKernelPowerTrace w (dworkQFrobeniusKernel k p w f) (power : ℕ) bound) atTop
      (nhds (NuclearOperator.tracePower w (dworkQFrobeniusNuclearOperator k p w f) power)) := by sorry
