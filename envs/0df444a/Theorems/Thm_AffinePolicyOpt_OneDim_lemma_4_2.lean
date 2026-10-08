-- Prove2me | Theorems.Thm_AffinePolicyOpt_OneDim_lemma_4_2
-- name    : AffinePolicyOpt.OneDim.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:07:55.039885+00:00
-- url     : https://prove2.me/theorems/98bd64aa-c97a-4e7f-add0-aefdb2b37a91
-- title:
--   Lemma 4.2, p. 11 — the maximum of (OPT) over Γ̃ is reached on the right side of Δ_Γ = conv{ṽ_0, …, ṽ_k}
-- statement:
--   Let $a,b\in\mathbb R^k$ satisfy the ordering (32), $a_0,b_0\in\mathbb R$, and $\theta=\pi(w)$ as in (23). Let $g:\mathbb R\to\mathbb R$ be convex, $c\ge0$, $L\le U$, and let $y^*$ minimize $c\,y+g(y)$ over $\mathbb R$; put $u^*(\theta_2)=\max(L,\min(U,y^*-\theta_2))$. Let
--   $$\tilde\Gamma=\big\{\big(\theta_1+c\,u^*(\theta_2),\ \theta_2+u^*(\theta_2)\big):(\theta_1,\theta_2)\in\Theta\big\},\qquad \Delta_\Gamma=\operatorname{conv}\{\tilde v_0,\dots,\tilde v_k\},$$
--   with $\tilde v_i$ the images of the right-side vertices $v_i=\pi(1,\dots,1,0,\dots,0)$ as in (29). Then the maximum of $\tilde\gamma_1+g(\tilde\gamma_2)$ over $\tilde\Gamma$ (problem (OPT)) is attained, and it equals the maximum of the same function over $\operatorname{r-side}(\Delta_\Gamma)$, which is also attained.
--
--   This reduces the search for the worst case after the optimal control is applied to the few points $\tilde v_i$ on the right side of $\Delta_\Gamma$, which Algorithm 1 then matches with an affine controller.
--
--   **Formalization Note** The statement is in the simplified notation of §4.1.1 under Assumptions 1–3 (unit hypercube, the ordering (32) of the generators). The optimal control law is the clamp of Lemma 7.1 for a minimizer $y^*$ (footnote 4 of the page assumes it unique; uniqueness is not needed). The convexity of $g$ is property P2.
-- source:
--   Bertsimas, Iancu & Parrilo, Optimality of Affine Policies in Multi-stage Robust Optimization, arXiv:0904.3986v1, p. 11, Lemma 4.2, with (26)–(29) (pp. 10–11)

import Mathlib
import Definitions.Def_AffinePolicyOpt_OneDim_Zonogon

namespace AffinePolicyOpt.OneDim

/-- Lemma 4.2: with `u* = clampLaw L U y*` for a minimizer `y*` of `c y + g(y)` (`g` convex), the
maximum of `γ̃_1 + g(γ̃_2)` over `Γ̃` (26) is attained, and equals the maximum over the right side
of `Δ_Γ = conv{ṽ_0, …, ṽ_k}` (28)–(29), which is also attained. -/
theorem lemma_4_2 (k : ℕ) (a0 b0 : ℝ) (a b : Fin k → ℝ) (hab : GenOrdered a b)
    (g : ℝ → ℝ) (hg : ConvexOn ℝ Set.univ g) (c L U ystar : ℝ) (hc : 0 ≤ c) (hLU : L ≤ U)
    (hy : IsMinOn (fun y => c * y + g y) Set.univ ystar) :
    ∃ μ : ℝ,
      IsGreatest ((fun γ : ℝ × ℝ => γ.1 + g γ.2) ''
          ((fun w => ((zon a0 b0 a b w).1 + c * clampLaw L U ystar (zon a0 b0 a b w).2,
              (zon a0 b0 a b w).2 + clampLaw L U ystar (zon a0 b0 a b w).2)) '' cube k)) μ ∧
      IsGreatest ((fun γ : ℝ × ℝ => γ.1 + g γ.2) ''
          rside (convexHull ℝ
            (Set.range (fun i : Fin (k + 1) => vtilde a0 b0 a b c L U ystar (i : ℕ))))) μ := by sorry

end AffinePolicyOpt.OneDim
