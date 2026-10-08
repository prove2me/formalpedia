-- Prove2me | Theorems.Thm_BellmanDP_ContGoldMining_lemma3_dominated_switching
-- name    : BellmanDP.ContGoldMining.lemma3_dominated_switching
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T17:42:57.153915+00:00
-- url     : https://prove2.me/theorems/73ed255b-835e-4704-8b4b-a91cc84e7df3
-- title:
--   Chapter VIII, Lemma 3 — if $K_i(t) < K_j(t)$ for some $j$ then $\varphi_i(t) = 0$
-- statement:
--   Consider the three-choice continuous gold-mining process with positive rates, initial amounts $x_0, y_0 \ge 0$ and a horizon $T$, finite ($T \ge 0$) or $T = \infty$. Let $\varphi$ be an admissible control maximizing $f(T)$ among all admissible controls, and $K_1, K_2, K_3$ its switching functions for that horizon (Eq. (12.5)). Then for almost every $t \in [0, T]$ ($t \ge 0$ when $T = \infty$) and every decision $i$,
--   $$K_i(t) < K_j(t) \ \text{ for some } j \implies \varphi_i(t) = 0.$$
--
--   An optimal control never uses a decision whose switching function is strictly beaten.
--
--   **Formalization Note** Both horizons, finite $T$ and $T = \infty$, as for Lemma 1. Decisions are indexed `0, 1, 2` for $A, B, C$.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter VIII, § 13, Lemma 3, p. 234

import Mathlib
import Definitions.Def_BellmanDP_ContGoldMining_Process
import Definitions.Def_BellmanDP_ContGoldMining_Switching

namespace BellmanDP.ContGoldMining

open MeasureTheory

/-- Bellman, *Dynamic Programming*, Ch. VIII, § 13, Lemma 3, p. 234: for an optimal control,
almost everywhere, if there is a `j` with `K_i(t) < K_j(t)` then `φ_i(t) = 0`. Stated for every
finite horizon `T` (with the `K_i` of Eq. (12.5)) and for `T = ∞`, the case § 12 considers. -/
theorem lemma3_dominated_switching (P : Params) (hP : P.Positive) (x₀ y₀ : ℝ) (hx₀ : 0 ≤ x₀)
    (hy₀ : 0 ≤ y₀) (φ : Control) :
    (∀ T : ℝ, 0 ≤ T → IsOptimalOn P x₀ y₀ T φ →
      ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)), ∀ i : Fin 3,
        (∃ j : Fin 3, switchingFn P x₀ y₀ φ T i t < switchingFn P x₀ y₀ φ T j t) →
          φ i t = 0) ∧
    (IsOptimalInfty P x₀ y₀ φ →
      ∀ᵐ t ∂(volume.restrict (Set.Ici 0)), ∀ i : Fin 3,
        (∃ j : Fin 3, switchingFnInfty P x₀ y₀ φ i t < switchingFnInfty P x₀ y₀ φ j t) →
          φ i t = 0) := by sorry

end BellmanDP.ContGoldMining
