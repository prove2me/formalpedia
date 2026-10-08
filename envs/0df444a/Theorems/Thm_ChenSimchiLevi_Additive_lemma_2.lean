-- Prove2me | Theorems.Thm_ChenSimchiLevi_Additive_lemma_2
-- name    : ChenSimchiLevi.Additive.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:41:38.050974+00:00
-- url     : https://prove2.me/theorems/55c967b9-e01b-46bf-bc9e-4971a2d981b0
-- title:
--   Lemma 2 — a maximizing expected demand $d_t(y)$ exists with $y - d_t(y)$ nondecreasing
-- statement:
--   Consider the model of Chen and Simchi-Levi (2004) under Assumptions 1–5 and additive demand ($\alpha_t = 1$ almost surely), and fix a period $t \in \{1, \dots, T\}$. Let $V : \mathbb R \to \mathbb R$ be any function playing the role of the continuation value $v_{t+1}$, and let
--   $$g_t(y, d) = R_t(d) - c_t y + \mathbb E\big\{-h_t(y - d - \beta_t) + V(y - d - \beta_t)\big\}.$$
--   Suppose $g_t(y, d)$ is jointly continuous in $(y, d) \in \mathbb R \times [\underline d_t, \bar d_t]$. Then there is a function $d_t : \mathbb R \to [\underline d_t, \bar d_t]$ such that
--
--   1. for every $y$, $d_t(y)$ maximizes $g_t(y, \cdot)$ over $[\underline d_t, \bar d_t]$, and
--   2. $y \mapsto y - d_t(y)$ is nondecreasing.
--
--   In words: the higher the inventory level after ordering, the higher the expected inventory at the end of the period. This monotone selection is what makes the expectation of a $k$-concave continuation value $k$-concave in the proof of Theorem 3.1.
--
--   **Formalization Note.** The lemma is stated for an arbitrary continuation $V$ rather than for $v_{t+1}$ only. It asserts the existence of one monotone selection of maximizers; it does not claim that every maximizer is monotone, which fails when $g_t(y, \cdot)$ has several maximizers.
-- source:
--   Chen, Simchi-Levi, Coordinating Inventory Control and Pricing Strategies with Random Demand and Fixed Ordering Cost: The Finite Horizon Case, Operations Research 52(6) (2004), p. 890, Lemma 2

import Mathlib
import Definitions.Def_ChenSimchiLevi_Additive_Model

open MeasureTheory

namespace ChenSimchiLevi.Additive

/-- Lemma 2 of Chen–Simchi-Levi (2004), p. 890, for an arbitrary continuation value `V` in place of
`v_{t+1}`: under additive demand, if `g_t(y, d)` is jointly continuous in `(y, d)`, there is a
maximizer `d_t(y)` of `g_t(y, ·)` over `[d_t, d̄_t]` for every `y` such that `y - d_t(y)` is
nondecreasing in `y`. -/
theorem lemma_2 (M : Model) (hA : M.Assumptions) (hadd : M.IsAdditive)
    (t : ℕ) (ht : t ∈ Finset.Icc 1 M.T) (V : ℝ → ℝ)
    (hcont : ContinuousOn (Function.uncurry (M.gWith V t))
      (Set.univ ×ˢ Set.Icc (M.dlo t) (M.dhi t))) :
    ∃ dsel : ℝ → ℝ,
      (∀ y : ℝ, dsel y ∈ Set.Icc (M.dlo t) (M.dhi t) ∧
        IsMaxOn (M.gWith V t y) (Set.Icc (M.dlo t) (M.dhi t)) (dsel y)) ∧
      Monotone (fun y => y - dsel y) := by sorry

end ChenSimchiLevi.Additive
