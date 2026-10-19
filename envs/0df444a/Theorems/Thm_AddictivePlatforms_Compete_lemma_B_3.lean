-- Prove2me | Theorems.Thm_AddictivePlatforms_Compete_lemma_B_3
-- name    : AddictivePlatforms.Compete.lemma_B_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T12:58:21.769857+00:00
-- url     : https://prove2.me/theorems/33c43a6e-f454-484b-8e8e-bcbd7365860c
-- title:
--   Lemma B.3, p. 29 — the incremental value U_2(x, y, d) of problem (A.3) is decreasing in d (integrated form)
-- statement:
--   Assume Assumptions 1–2 (with the mission's standing pins). Fix $d' \ge 0$ and a cap $\overline{A} > 0$. For $x, y > 0$ and $d \ge 0$ let
--   $$U(x,y,d) := \max_{(A_x,A_y)\in\mathbb{R}^2} \; x\cdot u\!\left(\frac{A_x}{x}, d\right) + y\cdot u\!\left(\frac{A_y}{y}, d'\right) - C(A_x + A_y) \quad \text{s.t. } A_x, A_y \ge 0,\ A_x + A_y \le \overline{A}. \qquad (A.3)$$
--   Then $U_2(x,y,d) = \partial U/\partial y$ is decreasing in $d$, in integrated form: for every $x > 0$ and $0 < y_1 < y_2$, the map
--   $$d \longmapsto U(x,y_2,d) - U(x,y_1,d)$$
--   is (weakly) decreasing on $[0,\infty)$.
--
--   In the proof of Proposition 2, $x = 1$ is a deviating platform with addictiveness $d$ and $y$ counts the other platforms at $d'$: lowering $d$ makes joining further platforms more attractive.
--
--   **Formalization Note.** $x$ and $y$ are positive reals, since they divide. The derivative claim is stated as a decreasing difference because the paper does not establish differentiability of $U$. The maximizer of (A.3) is a parameter `Astar` assumed to solve (A.3) for every $x, y > 0$ and $d \ge 0$.
-- source:
--   Ichihashi & Kim, Addictive Platforms, Bank of Canada SWP 2022-16 (Apr. 1, 2022), p. 29, Lemma B.3 and (A.3)

import Mathlib
import Definitions.Def_AddictivePlatforms_Compete_Model

open Set Filter Topology
open scoped ENNReal

namespace AddictivePlatforms.Compete

/-- Lemma B.3 (p. 29). Fix `d′ ≥ 0` and `Ā > 0`; let `(A_x*, A_y*)(x, y, d)` solve (A.3) and
`U(x, y, d)` be its value. Then `U₂(x, y, d)` is decreasing in `d`, stated in integrated form: for
`x > 0` and `0 < y₁ < y₂`, `U(x, y₂, d) − U(x, y₁, d)` is decreasing in `d ≥ 0`. -/
theorem lemma_B_3 (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C) (d' : ℝ) (hd' : 0 ≤ d')
    (Abar : ℝ≥0∞) (hAbar : 0 < Abar) (Astar : ℝ → ℝ → ℝ → ℝ × ℝ)
    (hA : ∀ x : ℝ, 0 < x → ∀ y : ℝ, 0 < y → ∀ d : ℝ, 0 ≤ d →
      IsB3Max u C Abar d' x y d (Astar x y d)) :
    ∀ x : ℝ, 0 < x → ∀ y₁ y₂ : ℝ, 0 < y₁ → y₁ < y₂ →
      AntitoneOn (fun d => objB3 u C d' x y₂ d (Astar x y₂ d).1 (Astar x y₂ d).2 -
        objB3 u C d' x y₁ d (Astar x y₁ d).1 (Astar x y₁ d).2) (Ici 0) := by sorry

end AddictivePlatforms.Compete
