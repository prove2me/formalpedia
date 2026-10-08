-- Prove2me | Theorems.Thm_BellmanDP_ContGoldMining_lemma1_switching_comparison
-- name    : BellmanDP.ContGoldMining.lemma1_switching_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T17:42:24.290496+00:00
-- url     : https://prove2.me/theorems/69540be0-9a06-4729-8856-98fcccf0ca2c
-- title:
--   Chapter VIII, Lemma 1 — if $K_i(t) > K_j(t)$ then $\varphi_i(t) = 1$ or $\varphi_j(t) = 0$
-- statement:
--   Consider the three-choice continuous gold-mining process with positive rates $q_1, q_2, q_3, r_1, r_2, r_3, r_4$, initial amounts $x_0, y_0 \ge 0$ and a horizon $T$, either finite ($T \ge 0$) or $T = \infty$. Let $\varphi = (\varphi_1, \varphi_2, \varphi_3)$ be an admissible control that maximizes $f(T)$ among all admissible controls, and let $K_1, K_2, K_3$ be the switching functions of Eq. (12.5) for that horizon, computed along $\varphi$. Then for almost every $t \in [0, T]$ (every $t \ge 0$ when $T = \infty$) and all decisions $i, j$,
--   $$K_i(t) > K_j(t) \implies \varphi_i(t) = 1 \ \text{ or } \ \varphi_j(t) = 0.$$
--
--   This is the basic first-order necessary condition of the chapter: an optimal control puts no weight on a decision whose switching function is beaten by another one. Lemmas 2 and 3 follow from it, and it drives the analysis of mixed policies in Lemmas 4 and 5.
--
--   **Formalization Note** The book announces that it considers only $T = \infty$ (§ 12) but writes the variation (12.4) and the switching functions (12.5) with a general $T$. The statement is the conjunction of both readings: every finite horizon $T \ge 0$ (`switchingFn`), and $T = \infty$ (`switchingFnInfty`, Eq. (12.5) with the boundary term $p(\infty)[\dots] = 0$). Decisions are indexed `0, 1, 2` for $A, B, C$.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter VIII, § 13, Lemma 1, p. 234

import Mathlib
import Definitions.Def_BellmanDP_ContGoldMining_Process
import Definitions.Def_BellmanDP_ContGoldMining_Switching

namespace BellmanDP.ContGoldMining

open MeasureTheory

/-- Bellman, *Dynamic Programming*, Ch. VIII, § 13, Lemma 1, p. 234: for an optimal control,
almost everywhere, if `K_i(t) > K_j(t)` then `φ_i(t) = 1` or `φ_j(t) = 0`. Stated for every
finite horizon `T` (with the `K_i` of Eq. (12.5)) and for `T = ∞`, the case § 12 considers. -/
theorem lemma1_switching_comparison (P : Params) (hP : P.Positive) (x₀ y₀ : ℝ) (hx₀ : 0 ≤ x₀)
    (hy₀ : 0 ≤ y₀) (φ : Control) :
    (∀ T : ℝ, 0 ≤ T → IsOptimalOn P x₀ y₀ T φ →
      ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)), ∀ i j : Fin 3,
        switchingFn P x₀ y₀ φ T j t < switchingFn P x₀ y₀ φ T i t → φ i t = 1 ∨ φ j t = 0) ∧
    (IsOptimalInfty P x₀ y₀ φ →
      ∀ᵐ t ∂(volume.restrict (Set.Ici 0)), ∀ i j : Fin 3,
        switchingFnInfty P x₀ y₀ φ j t < switchingFnInfty P x₀ y₀ φ i t →
          φ i t = 1 ∨ φ j t = 0) := by sorry

end BellmanDP.ContGoldMining
