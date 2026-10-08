-- Prove2me | Theorems.Thm_AffinePolicyOpt_OneDim_lemma_4_1
-- name    : AffinePolicyOpt.OneDim.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:07:51.627864+00:00
-- url     : https://prove2.me/theorems/a818ff14-3fea-4986-a418-29ba2a393e5a
-- title:
--   Lemma 4.1, p. 8 — the maximum of θ₁ + f(θ₂) over the zonogon is attained at a right-side vertex v_n = π(1,…,1,0,…,0)
-- statement:
--   Let $k\ge0$, let $a,b\in\mathbb R^k$ satisfy the ordering (32) ($b_i\ge0$ and $a_1/b_1>\dots>a_k/b_k$), let $a_0,b_0\in\mathbb R$, and let $\pi(w)=\big(a_0+\sum_ia_iw_i,\ b_0+\sum_ib_iw_i\big)$. For every convex $f:\mathbb R\to\mathbb R$ there is $n\in\{0,\dots,k\}$ such that the hypercube vertex $e_{\le n}=(1,\dots,1,0,\dots,0)$ (ones in the first $n$ coordinates) maximizes
--   $$w\mapsto \theta_1(w)+f(\theta_2(w))$$
--   over $w\in[0,1]^k$.
--
--   Equivalently, the maximum of $\theta_1+f(\theta_2)$ over the zonogon $\Theta=\pi([0,1]^k)$ is attained at one of $v_0,\dots,v_k$, the vertices on its right side. In the paper $f=J^*_{k+1}$ and this lemma reduces the $2^k$ vertices of the disturbance box to $k+1$ candidate points.
--
--   **Formalization Note** The page states the lemma inside the induction step, under Assumptions 1–3 of p. 10 (unit hypercube, maximal number of vertices, and the vertex $v_i$ being the image of $e_{\le i}$), which the paper introduces as normalizations without loss of generality. The Lean statement takes the unit hypercube and the ordering (32), written cross-multiplied so that $b_i=0$ is meaningful, and states the conclusion for any convex $f$, as Corollary 4.1 uses it.
-- source:
--   Bertsimas, Iancu & Parrilo, Optimality of Affine Policies in Multi-stage Robust Optimization, arXiv:0904.3986v1, p. 8, Lemma 4.1, with (18)–(20), (23), (32) and Assumptions 1–3 (p. 10)

import Mathlib
import Definitions.Def_AffinePolicyOpt_OneDim_Zonogon

namespace AffinePolicyOpt.OneDim

/-- Lemma 4.1: for generators ordered as in (32) and any convex `f`, the maximum of
`θ_1 + f(θ_2)` over the zonogon `Θ = π([0,1]^k)` is attained at one of the points
`v_n = π([1,…,1,0,…,0])`, `n ∈ {0, …, k}`. -/
theorem lemma_4_1 (k : ℕ) (a0 b0 : ℝ) (a b : Fin k → ℝ) (hab : GenOrdered a b)
    (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) :
    ∃ n ≤ k, IsMaxOn (fun w => (zon a0 b0 a b w).1 + f (zon a0 b0 a b w).2)
      (cube k) (prefixVertex k n) := by sorry

end AffinePolicyOpt.OneDim
