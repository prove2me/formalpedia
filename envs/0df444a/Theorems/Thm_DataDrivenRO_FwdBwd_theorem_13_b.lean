-- Prove2me | Theorems.Thm_DataDrivenRO_FwdBwd_theorem_13_b
-- name    : DataDrivenRO.FwdBwd.theorem_13_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:02:59.428521+00:00
-- url     : https://prove2.me/theorems/a6999806-e233-465f-be8c-289ec1bec9ff
-- title:
--   Theorem 13(b), p. 29 — the constraint δ*(v|𝒰^{FB}_ε) ≤ t is bi-convex in (v,t) and ε, for 0 < ε < 1/√e
-- statement:
--   Let $m_b\le m_f$ and $\bar\sigma_f,\bar\sigma_b>0$ in $\mathbb R^d$. For $0<\varepsilon<1/\sqrt e$:
--
--   1. the set $\{(v,t)\in\mathbb R^d\times\mathbb R : \delta^*(v\mid\mathcal U^{FB}_\varepsilon)\le t\}$ is convex;
--   2. for each fixed $v$, the function $\varepsilon\mapsto\delta^*(v\mid\mathcal U^{FB}_\varepsilon)$ is convex on the interval $(0,1/\sqrt e)$.
--
--   That is, the constraint $\delta^*(v\mid\mathcal U^{FB}_\varepsilon)\le t$ is convex in $(v,t)$ for fixed $\varepsilon$, and its left-hand side is a convex function of $\varepsilon$ for fixed $(v,t)$. This justifies the alternating heuristic of §9 for optimising the levels $\varepsilon_j$ of several constraints.
--
--   **Formalization Note** "Bi-convex constraint" is read as the two convexity statements above: in $(v,t)$, convexity of the feasible set; in $\varepsilon$, convexity of the constraint function $\varepsilon\mapsto\delta^*(v\mid\mathcal U^{FB}_\varepsilon)$ on $(0,1/\sqrt e)$, which is what the proof (EC.1.8) establishes ("convex in $\epsilon$ … whenever $\sqrt{2\log(1/\epsilon)}$ is convex"). Convexity of the sublevel set in $\varepsilon$ alone would hold on all of $(0,1)$, because $\delta^*$ decreases in $\varepsilon$, and would not use the threshold $1/\sqrt e$. $1/\sqrt e$ is written $e^{-1/2}$. The proof's "$0<\epsilon<1\sqrt e$" is a misprint for $1/\sqrt e$.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 13(b), p. 29; proof EC.1.8, p. ec9

import Mathlib
import Definitions.Def_DataDrivenRO_FwdBwd_Setting

namespace DataDrivenRO.FwdBwd

theorem theorem_13_b {d : ℕ} (mb mf sf sb : Fin d → ℝ) (hm : ∀ i, mb i ≤ mf i)
    (hsf : ∀ i, 0 < sf i) (hsb : ∀ i, 0 < sb i) :
    (∀ ε : ℝ, ε ∈ Set.Ioo 0 (Real.exp (-1 / 2)) →
      Convex ℝ {p : (Fin d → ℝ) × ℝ |
        RobustMDP.Shared.supportFunction (UFB mb mf sf sb ε) p.1 ≤ p.2}) ∧
    (∀ v : Fin d → ℝ,
      ConvexOn ℝ (Set.Ioo 0 (Real.exp (-1 / 2)))
        (fun ε : ℝ => RobustMDP.Shared.supportFunction (UFB mb mf sf sb ε) v)) := by sorry

end DataDrivenRO.FwdBwd
