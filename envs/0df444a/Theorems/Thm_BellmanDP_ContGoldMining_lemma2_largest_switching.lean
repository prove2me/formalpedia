-- Prove2me | Theorems.Thm_BellmanDP_ContGoldMining_lemma2_largest_switching
-- name    : BellmanDP.ContGoldMining.lemma2_largest_switching
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T17:42:03.893423+00:00
-- url     : https://prove2.me/theorems/9728caf0-474c-4aa4-a56f-6c78e535d589
-- title:
--   Chapter VIII, Lemma 2 — if $K_i(t)$ is strictly largest then $\varphi_i(t) = 1$
-- statement:
--   Consider the three-choice continuous gold-mining process with positive rates, initial amounts $x_0, y_0 \ge 0$ and a horizon $T$, finite ($T \ge 0$) or $T = \infty$. Let $\varphi$ be an admissible control maximizing $f(T)$ among all admissible controls, and $K_1, K_2, K_3$ its switching functions for that horizon (Eq. (12.5)). Then for almost every $t \in [0, T]$ ($t \ge 0$ when $T = \infty$) and every decision $i$,
--   $$K_i(t) > K_j(t) \ \text{ for all } j \ne i \implies \varphi_i(t) = 1.$$
--
--   An optimal control uses exclusively the decision whose switching function is strictly the largest.
--
--   **Formalization Note** Both horizons, finite $T$ and $T = \infty$, as for Lemma 1. Decisions are indexed `0, 1, 2` for $A, B, C$.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter VIII, § 13, Lemma 2, p. 234

import Mathlib
import Definitions.Def_BellmanDP_ContGoldMining_Process
import Definitions.Def_BellmanDP_ContGoldMining_Switching

namespace BellmanDP.ContGoldMining

open MeasureTheory

/-- Bellman, *Dynamic Programming*, Ch. VIII, § 13, Lemma 2, p. 234: for an optimal control,
almost everywhere, if `K_i(t) > K_j(t)` for all `j ≠ i` then `φ_i(t) = 1`. Stated for every
finite horizon `T` (with the `K_i` of Eq. (12.5)) and for `T = ∞`, the case § 12 considers. -/
theorem lemma2_largest_switching (P : Params) (hP : P.Positive) (x₀ y₀ : ℝ) (hx₀ : 0 ≤ x₀)
    (hy₀ : 0 ≤ y₀) (φ : Control) :
    (∀ T : ℝ, 0 ≤ T → IsOptimalOn P x₀ y₀ T φ →
      ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)), ∀ i : Fin 3,
        (∀ j : Fin 3, j ≠ i → switchingFn P x₀ y₀ φ T j t < switchingFn P x₀ y₀ φ T i t) →
          φ i t = 1) ∧
    (IsOptimalInfty P x₀ y₀ φ →
      ∀ᵐ t ∂(volume.restrict (Set.Ici 0)), ∀ i : Fin 3,
        (∀ j : Fin 3, j ≠ i → switchingFnInfty P x₀ y₀ φ j t < switchingFnInfty P x₀ y₀ φ i t) →
          φ i t = 1) := by sorry

end BellmanDP.ContGoldMining
