-- Prove2me | Theorems.Thm_AtaBarjesteh23_Workload_corollary_2
-- name    : AtaBarjesteh23.Workload.corollary_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:13.497775+00:00
-- url     : https://prove2.me/theorems/53c420bc-cb91-4fbc-849c-7d87469497c9
-- title:
--   Corollary 2, p. 20 — f is strictly decreasing, strictly convex, C², solves (37)–(39), and is unique up to an additive constant
-- statement:
--   Assume the standing assumptions and let $f(w)=\int_{l_{\gamma^\star}}^w v(x)\,dx$ (55). On $[l_{\gamma^\star},u_{\gamma^\star}]$, $f$ is strictly decreasing, strictly convex and twice continuously differentiable, and $(l_{\gamma^\star},u_{\gamma^\star},\gamma^\star,f)$ solves the Bellman equation
--   $$\min_{x\in\mathbb R}\Big\{\tfrac12\sigma^2f''(w)+\mu f'(w)-xf'(w)+c(x)+h(w)\Big\}=\gamma,\quad w\in(l,u), \tag{37}$$
--   with $f'(l)=-\kappa$, $f'(u)=0$ (38) and $f''(l)=f''(u)=0$ (39). Moreover, whenever $(l,u,\gamma,g)$ solves (37)–(39), then $l=l_{\gamma^\star}$, $u=u_{\gamma^\star}$, $\gamma=\gamma^\star$ and $g=f+C$ on $[l,u]$ for some constant $C$.
--
--   $f$ is the relative value function of the EWF; it is the test function in the verification proof of Theorem 1.
--
--   **Formalization Note** The minimum in (37) is stated as attained (`IsLeast`). Uniqueness up to an additive constant is read for the quadruple $(l,u,\gamma,f)$, as Proposition 3 does for $v$.
-- source:
--   Ata and Barjesteh, An Approximate Analysis of Dynamic Pricing, Outsourcing, and Scheduling Policies for a Multiclass Make-to-Stock Queue in the Heavy Traffic Regime, accepted manuscript (SSRN 3464763; published in Operations Research 71(1):341–357, 2023, doi:10.1287/opre.2022.2361), p. 20, Corollary 2, (37)–(39), (55)

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting

open Set

namespace AtaBarjesteh23.Workload

theorem corollary_2 (M : Model) (hM : M.Standing) :
    StrictAntiOn M.fStar (Icc M.lStar M.uStar) ∧
    StrictConvexOn ℝ (Icc M.lStar M.uStar) M.fStar ∧
    ContDiffOn ℝ 2 M.fStar (Icc M.lStar M.uStar) ∧
    M.BellmanF M.lStar M.uStar M.gammaStar M.fStar ∧
    ∀ (l u γ : ℝ) (g : ℝ → ℝ), M.BellmanF l u γ g →
      l = M.lStar ∧ u = M.uStar ∧ γ = M.gammaStar ∧
        ∃ C : ℝ, ∀ w ∈ Icc l u, g w = M.fStar w + C := by sorry

end AtaBarjesteh23.Workload
