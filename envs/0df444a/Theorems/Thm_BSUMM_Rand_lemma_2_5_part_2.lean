-- Prove2me | Theorems.Thm_BSUMM_Rand_lemma_2_5_part_2
-- name    : BSUMM.Rand.lemma_2_5_part_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:07.455375+00:00
-- url     : https://prove2.me/theorems/df5c7f30-0739-4ad1-b826-663cecde273f
-- title:
--   Lemma 2.5(2) — E[Δ_d^t − Δ_d^{t−1} | z^{t−1}] ≤ −α^{t−1}p₀(Ex^{t−1} − q)ᵀ(Ex̄^t − q) for RBSUM-M
-- statement:
--   Assume Assumption A and let $(p_0,\dots,p_K)$ be a probability vector with all $p_k>0$. For RBSUM-M, with the dual gap $\Delta_d^t=d^*-d(y^t)$,
--
--   $$\mathbb E\big[\Delta_d^t-\Delta_d^{t-1}\,\big|\,z^{t-1}\big]\ \le\ -\alpha^{t-1}p_0\,(Ex^{t-1}-q)^\top(E\bar x^t-q), \tag{2.18}$$
--
--   where $\hat y^t=y^{t-1}+\alpha^{t-1}(q-Ex^{t-1})$ and $\bar x^t$ is any point of $X(\hat y^t)$.
--
--   Only the dual update changes $y$, so the expected change of the dual gap is $p_0\,(d(y^{t-1})-d(\hat y^t))$; the bound links it to the constraint residual at the current and the next dual point.
--
--   **Formalization Note** Stated at an arbitrary state $(x,y)=z^{t-1}$ with stepsize $a=\alpha^{t-1}>0$, as the one-step average $p_0\,[\Delta_d(\hat y)-\Delta_d(y)]+\sum_k p_k\,[\Delta_d(y)-\Delta_d(y)]$; the primal branches contribute zero, so the block steps entering the average are arbitrary. The bound holds for every $\bar x\in X(\hat y)$ (the page's $\bar x^t$ is the one nearest to $x^t$; $E\bar x$ is the same for all of them).
-- source:
--   Hong, Chang, Wang, Razaviyayn, Ma, Luo, arXiv:1401.7079v1, p. 13, Lemma 2.5 (2.18)

import Mathlib
import Definitions.Def_BSUMM_Rand_Setting
import Definitions.Def_BSUMM_Rand_RBSUMM

open scoped RealInnerProductSpace

namespace BSUMM.Rand

/-- Lemma 2.5(2) (arXiv:1401.7079v1, p. 13, (2.18)), in operator form at the state
`z^{t-1} = (x, y)` with `a = α^{t-1}` and `ŷ = ŷ^t = y + a(q - Ex)`: the one-step average of
`Δ_d^t - Δ_d^{t-1}` is at most `-α^{t-1} p_0 (Ex^{t-1} - q)ᵀ(E x̄^t - q)` for every `x̄^t ∈ X(ŷ^t)`.
Only the dual branch moves `y`, so the block steps `x̂` are arbitrary. -/
theorem lemma_2_5_part_2 (S : Setting) (hA : S.AssumptionA) (p : Fin (S.K + 1) → ℝ)
    (hp : S.IsProbVec p) (x : S.Xsp) (y : S.Ysp) (a : ℝ) (ha : 0 < a) (xhat : S.Xsp)
    (xbar : S.Xsp) (hxbar : xbar ∈ S.Xopt (S.dualStep x y a)) :
    S.condAvg p (fun _ y' => S.DeltaD y' - S.DeltaD y) x y a xhat ≤
      -(a * p 0) * ⟪S.Emap x - S.q, S.Emap xbar - S.q⟫ := by sorry

end BSUMM.Rand
