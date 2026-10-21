-- Prove2me | Theorems.Thm_FiniteFields_Dwork_dworkPowerSeriesEval_rescale
-- name    : FiniteFields.Dwork.dworkPowerSeriesEval_rescale
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T01:41:52.547626+00:00
-- url     : https://prove2.me/theorems/cf2a08c3-1c1c-435c-ae48-a772cb24028f
-- title:
--   Evaluating $f(rX)$ at $x$ equals evaluating $f$ at $rx$
-- statement:
--   Let $p$ be a prime and $k$ a finite field of characteristic $p$, with $q=|k|=p^a$ elements, $a=[k:\mathbb F_p]$. Write $W(k)$ for the ring of $p$-typical Witt vectors of $k$, $F$ for its Witt vector Frobenius, $K$ for the completion of the fraction field of $W(k)$ with respect to its $p$-adic valuation, and $\sigma$ for the continuous extension of $F$ to $K$. Let $L=K(\zeta)$ be the $p$-th cyclotomic extension of $K$, where $\zeta\in L$ is a fixed primitive $p$-th root of unity, equipped with the spectral norm $|\cdot|$ extending the absolute value of $K$. For $x\in k$, write $\hat x\in L$ for the image of the Teichmüller representative $[x]\in W(k)$.
--
--   For a formal power series $f(X)=\sum_{n\ge0}a_nX^n\in L[[X]]$ and a point $x\in L$, define the evaluation
--   $$f(x)=\sum_{n\ge0}a_n x^n\in L,$$
--   the sum being taken in the complete normed field $L$. For $r\in L$ let $f(rX)=\sum_{n\ge0}r^na_nX^n$ denote the rescaled series. Then for all $f\in L[[X]]$ and all $r,x\in L$,
--   $$\big(f(rX)\big)(x)=f(rx),\qquad\text{i.e.}\qquad\sum_{n\ge0}r^na_n\,x^n=\sum_{n\ge0}a_n\,(rx)^n .$$
--
--   This identity is used to evaluate Dwork's splitting series $\theta(X)=\mathbb E(\eta X)$, which is a rescaling of the Artin–Hasse series, at points of the $p$-adic unit ball.
--
--   **Formalization Note** The evaluation is defined as an unconditional sum (`tsum`), which Lean assigns the value $0$ when the family is not summable. The two families above have identical terms, so the identity holds for all $f$, $r$, $x$, with no convergence hypothesis.
-- source:
--   B. Dwork, *On the rationality of the zeta function of an algebraic variety*, Amer. J. Math. 82 (1960), 631–648, §1 (evaluation of the splitting series $\theta(t)$); auxiliary lemma in the formalization of §1, with no direct counterpart in the paper. Lean: ported from the `finite_fields` project (commit e8b5bf14), file `WeilConjectures/Dwork/AnalyticEvaluation.lean`, declaration `WeilConjectures.Dwork.dworkPowerSeriesEval_rescale`

import Mathlib
import Definitions.Def_FiniteFields_Dwork_ArtinHasse

open Filter PowerSeries
open scoped NNReal Topology
open FiniteFields.Dwork
variable (k : Type*) [Field k]
variable (p : ℕ) [Fact p.Prime] [CharP k p] [Finite k]

theorem FiniteFields.Dwork.dworkPowerSeriesEval_rescale
    (f : (DworkCyclotomicField k p)⟦X⟧)
    (r x : DworkCyclotomicField k p) :
    dworkPowerSeriesEval k p (PowerSeries.rescale r f) x =
      dworkPowerSeriesEval k p f (r * x) := by sorry
