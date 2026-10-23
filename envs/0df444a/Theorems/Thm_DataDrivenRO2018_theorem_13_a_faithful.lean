-- Prove2me | Theorems.Thm_DataDrivenRO2018_theorem_13_a_faithful
-- name    : DataDrivenRO2018.theorem_13_a_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T03:22:28.028353+00:00
-- url     : https://prove2.me/theorems/af4e7d63-dc8d-4fd2-b382-1caaa2e69690
-- title:
--   Theorem 13(a): the $\mathcal U^{CS}_\varepsilon$ constraint is bi-convex for $0<\varepsilon<3/4$
-- statement:
--   Let $\hat\mu\in\mathbb R^d$, $\Gamma_1,\Gamma_2\ge0$, and let $C$ be a $d\times d$ matrix with $C^\top C=\hat\Sigma+\Gamma_2I$. For $0<\varepsilon<1$ let
--
--   $$\mathcal U^{CS}_\varepsilon=\{\hat\mu+y+C^\top w:\ \|y\|_2\le\Gamma_1,\ \|w\|_2\le\sqrt{1/\varepsilon-1}\}$$
--
--   and let $\delta^*(v\mid\mathcal U)=\sup_{u\in\mathcal U}v^\top u$. Then the constraint function $g(v,t,\varepsilon)=\delta^*(v\mid\mathcal U^{CS}_\varepsilon)-t$ is bi-convex on $0<\varepsilon<3/4$:
--
--   1. for each fixed $\varepsilon\in(0,3/4)$, $(v,t)\mapsto g(v,t,\varepsilon)$ is convex on $\mathbb R^d\times\mathbb R$;
--   2. for each fixed $(v,t)$, $\varepsilon\mapsto g(v,t,\varepsilon)$ is convex on $(0,3/4)$.
--
--   This is Theorem 13(a) of Bertsimas, Gupta and Kallus, which underlies the alternating heuristic of §9 for problems with several chance constraints whose levels $\varepsilon_j$ are also optimized. It complements the support formula of Theorem 10 (DataDrivenRO.Moment.theorem_10), by which $g(v,t,\varepsilon)=\hat\mu^\top v+\Gamma_1\|v\|_2+\sqrt{(1-\varepsilon)/\varepsilon}\,\sqrt{v^\top(\hat\Sigma+\Gamma_2I)v}-t$.
--
--   **Formalization Note** "Bi-convex constraint $\delta^*\le t$" is read as bi-convexity of the constraint function $\delta^*(v\mid\mathcal U^{CS}_\varepsilon)-t$; the threshold $0.75$ is where $\varepsilon\mapsto\sqrt{1/\varepsilon-1}$ stops being convex. The support function is the real supremum of the published definition, genuine here because $\mathcal U^{CS}_\varepsilon$ is nonempty and compact.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, Mathematical Programming 167 (2018), doi:10.1007/s10107-017-1125-8 (arXiv:1401.0212v2), §9, p. 29, Theorem 13(a)

import Mathlib
import Definitions.Def_DataDrivenRO_Moment_Setting
import Definitions.Def_RobustMDP_Shared_supportFunction

theorem DataDrivenRO2018.theorem_13_a_faithful {d : ℕ} (Γ₁ Γ₂ : ℝ)
    (μhat : Fin d → ℝ) (Shat C : Matrix (Fin d) (Fin d) ℝ)
    (hΓ₁ : 0 ≤ Γ₁) (hΓ₂ : 0 ≤ Γ₂)
    (hC : C.transpose * C = Shat + Γ₂ • (1 : Matrix (Fin d) (Fin d) ℝ)) :
    (∀ ε : ℝ, 0 < ε → ε < 3 / 4 →
      ConvexOn ℝ Set.univ (fun p : (Fin d → ℝ) × ℝ =>
        RobustMDP.Shared.supportFunction (DataDrivenRO.Moment.UCS μhat C Γ₁ ε) p.1 - p.2)) ∧
    (∀ (v : Fin d → ℝ) (t : ℝ),
      ConvexOn ℝ (Set.Ioo (0 : ℝ) (3 / 4)) (fun ε : ℝ =>
        RobustMDP.Shared.supportFunction (DataDrivenRO.Moment.UCS μhat C Γ₁ ε) v - t)) := by sorry
