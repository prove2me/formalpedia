-- Prove2me | Theorems.Thm_AtaBarjesteh23_Workload_proposition_3
-- name    : AtaBarjesteh23.Workload.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:17.575807+00:00
-- url     : https://prove2.me/theorems/033f4777-6244-424b-a986-009a22ae5b04
-- title:
--   Proposition 3, p. 20 — v is non-positive, strictly increasing, C¹ on [l_γ⋆, u_γ⋆], and (l_γ⋆, u_γ⋆, γ⋆, v) uniquely solves (43)–(45)
-- statement:
--   Assume the standing assumptions and let $v$ be the function (54) built from $v^-_{\gamma^\star}$ and $v^+_{\gamma^\star}$. Then on $[l_{\gamma^\star},u_{\gamma^\star}]$ the function $v$ is non-positive, strictly increasing and continuously differentiable, and $(l_{\gamma^\star},u_{\gamma^\star},\gamma^\star,v)$ solves the Bellman equation (43)–(45). Moreover it is the unique solution: whenever $(l,u,\gamma,\tilde v)$ solves (43)–(45),
--   $$l=l_{\gamma^\star},\qquad u=u_{\gamma^\star},\qquad \gamma=\gamma^\star,\qquad \tilde v=v\ \text{on }[l,u].$$
--
--   Proposition 3 identifies the solution of the Bellman equation in Riccati form; the candidate drift (56) is $\frac{m'H^{-1}m}{2}v$.
--
--   **Formalization Note** "Unique" is read for the quadruple $(l,u,\gamma,v)$, with $v$ compared on $[l,u]$ (values outside the interval are irrelevant).
-- source:
--   Ata and Barjesteh, An Approximate Analysis of Dynamic Pricing, Outsourcing, and Scheduling Policies for a Multiclass Make-to-Stock Queue in the Heavy Traffic Regime, accepted manuscript (SSRN 3464763; published in Operations Research 71(1):341–357, 2023, doi:10.1287/opre.2022.2361), p. 20, Proposition 3, (43)–(45), (54)

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting

open Set

namespace AtaBarjesteh23.Workload

theorem proposition_3 (M : Model) (hM : M.Standing) :
    (∀ w ∈ Icc M.lStar M.uStar, M.vStar w ≤ 0) ∧
    StrictMonoOn M.vStar (Icc M.lStar M.uStar) ∧
    ContDiffOn ℝ 1 M.vStar (Icc M.lStar M.uStar) ∧
    M.BellmanV M.lStar M.uStar M.gammaStar M.vStar ∧
    ∀ (l u γ : ℝ) (v : ℝ → ℝ), M.BellmanV l u γ v →
      l = M.lStar ∧ u = M.uStar ∧ γ = M.gammaStar ∧ EqOn v M.vStar (Icc l u) := by sorry

end AtaBarjesteh23.Workload
