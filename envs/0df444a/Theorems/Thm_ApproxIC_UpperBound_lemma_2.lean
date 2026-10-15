-- Prove2me | Theorems.Thm_ApproxIC_UpperBound_lemma_2
-- name    : ApproxIC.UpperBound.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:30.883637+00:00
-- url     : https://prove2.me/theorems/ecfe1183-6c80-4cd9-81ee-b151a151671f
-- title:
--   Lemma 2, p. 20 — λ^IC(v) = d/dv Σ_{j=0}^k F(w^j(v)) on the k-th step solves the functional equation of (D)
-- statement:
--   Assume the standing density assumptions and fix a path $(\mu,\nu_0,v^\star,w)$, with thresholds $\nu_{-1}=\bar v$, $\nu_{k-1}=w(\nu_k)$, and number of steps $K$ (the first index with $\nu_K\le\mu$). Define $\lambda^\star$ on $[\mu,\bar v]$ by
--   $$\lambda^\star(v)=\frac{d}{dv}\sum_{j=0}^{k}F(w^j(v))\qquad\text{on the step }[\nu_k,\nu_{k-1}],\ k\in\{0,\dots,K\},$$
--   where $w^j$ is the $j$-th iterate of $w$ and $w^0(v)=v$. Then:
--   1. $\lambda^\star$ is feasible for the dual problem (D): $\lambda^\star\ge 0$ on $[\mu,\bar v]$, $\lambda^\star=f$ a.e. on $[\nu_0,\bar v]$, and $\lambda^\star(v)=f(v)+\dot w(v)\lambda^\star(w(v))$ a.e. on $[\mu,\nu_0]$;
--   2. for every $k\in\{0,\dots,K\}$, the formula above holds almost everywhere on $[\nu_k,\nu_{k-1}]\cap[\mu,\infty)$.
--
--   This explicit solution of the functional equation is what makes $\Phi_1$ and $\Phi_2$ computable in Lemmas 3 and 4.
--
--   **Formalization Note** The thresholds are the $\mathbb N$-indexed sequence `nuSeq` with `nuSeq 0` $=\bar v$; the paper's $\nu_k$ is `nuSeq (k+1)` and the step $[\nu_k,\nu_{k-1}]$ is `Set.Icc (nuSeq P (k+1)) (nuSeq P k)`. "A solution to Problem (D)" is read as a feasible point of (D). $\lambda^\star$ is defined pointwise with the step index of $v$ (the least $k$ with $\nu_k\le v$, capped at $K$); clause 2 is the paper's displayed formula.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), p. 20, Lemma 2; thresholds p. 19

import Mathlib
import Definitions.Def_ApproxIC_UpperBound_Path

namespace ApproxIC.UpperBound

open MeasureTheory

theorem lemma_2 (M : Model) (hM : M.Standing) (P : Path M) :
    DualFeasible M P (lamStar M P) ∧
    ∀ k ≤ steps P,
      ∀ᵐ v ∂(volume.restrict (Set.Icc (nuSeq P (k + 1)) (nuSeq P k) ∩ Set.Ici P.mu)),
        lamStar M P v = deriv (fun u => ∑ j ∈ Finset.range (k + 1), cdf M (P.w^[j] u)) v := by sorry

end ApproxIC.UpperBound
