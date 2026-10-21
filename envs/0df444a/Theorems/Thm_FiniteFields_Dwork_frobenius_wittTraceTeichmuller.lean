-- Prove2me | Theorems.Thm_FiniteFields_Dwork_frobenius_wittTraceTeichmuller
-- name    : FiniteFields.Dwork.frobenius_wittTraceTeichmuller
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T01:53:02.004289+00:00
-- url     : https://prove2.me/theorems/15b5e107-4e60-4eb3-9ca5-e8f89d321f9f
-- title:
--   The Witt trace vector $\sum_{i<a}[F^i[x]]$ is fixed by Witt Frobenius
-- statement:
--   Let $p$ be a prime and $k$ a finite field of characteristic $p$ with $q=p^a$ elements, $a=[k:\mathbb F_p]$. Let $W(k)$ be the ring of $p$-typical Witt vectors of $k$, with Witt vector Frobenius $F$ and Teichmüller representatives $[x]\in W(k)$ for $x\in k$. Let $W(W(k))$ be the ring of $p$-typical Witt vectors with coefficients in $W(k)$, with Teichmüller map $r\mapsto[r]$ and Witt vector Frobenius $\mathbf F$ (the Frobenius of Witt vectors over the characteristic-zero ring $W(k)$). For $x\in k$ consider the Witt vector
--   $$\tau(x)=\sum_{i=0}^{a-1}\big[F^{i}([x])\big]\in W(W(k)),$$
--   the sum (in the ring $W(W(k))$) of the Teichmüller vectors of the Frobenius conjugates $F^i([x])\in W(k)$ of the Teichmüller representative $[x]\in W(k)$. Then
--   $$\mathbf F\big(\tau(x)\big)=\tau(x).$$
--
--   Frobenius shifts the orbit $[x],F([x]),\dots,F^{a-1}([x])$ by one step, and the orbit closes up after $a$ steps. Frobenius invariance makes the Artin–Hasse functional equation available for $\tau(x)$, which is needed to evaluate Dwork's product $\prod_{i<a}\theta\big(\widehat{x^{p^i}}\big)$ (formulas (7)–(8)).
--
--   **Formalization Note** $\mathbf F$ is Mathlib's `WittVector.frobenius` on $W(R)$ with $R=W(k)$, and the inner Frobenius $F$ is `WittVector.frobenius` on $W(k)$; $a$ is `Module.finrank (ZMod p) k`.
-- source:
--   B. Dwork, *On the rationality of the zeta function of an algebraic variety*, Amer. J. Math. 82 (1960), 631–648, §1, formulas (7)–(8) (Frobenius conjugates in the additive character); auxiliary lemma in the formalization of (8), with no direct counterpart in the paper. Lean: ported from the `finite_fields` project (commit e8b5bf14), file `WeilConjectures/Dwork/WittTraceCharacter/TraceLimit.lean`, declaration `WeilConjectures.Dwork.frobenius_wittTraceTeichmuller`

import Mathlib
import Definitions.Def_FiniteFields_Dwork_AdditiveCharacter

open PowerSeries IsUltrametricDist
open FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
attribute [local instance] FiniteFields.Dwork.dw4e2TraceLimitResiduePrimeAlgebra

theorem FiniteFields.Dwork.frobenius_wittTraceTeichmuller (x : k) :
    WittVector.frobenius (wittTraceTeichmuller k p (teichmullerLift k p x))
      = wittTraceTeichmuller k p (teichmullerLift k p x) := by sorry
