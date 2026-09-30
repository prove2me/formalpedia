-- Prove2me | Theorems.Thm_AlgMechDesign_LowerBound_independence
-- name    : AlgMechDesign.LowerBound.independence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T18:44:30.710218+00:00
-- url     : https://prove2.me/theorems/b9cc28cc-d135-4d7a-9f0c-70badfa9cf13
-- title:
--   Proposition 4.4 (Independence) — payments depend only on the allocated set
-- statement:
--   Let $(x,p)$ be a truthful direct mechanism for task scheduling, let $t_1$ and $t_2$ be positive type vectors and let $i$ be an agent. If $t_1$ and $t_2$ agree on every agent other than $i$ ($t_1^{-i} = t_2^{-i}$) and give agent $i$ the same set of tasks ($x^i(t_1) = x^i(t_2)$), then agent $i$ receives the same payment:
--
--   $$
--   p^i(t_1) = p^i(t_2).
--   $$
--
--   This makes the price $p^i(X, t^{-i})$ of Definition 12 independent of the declaration used to attain $X$, so that a truthful mechanism can be described by its prices.
--
--   **Formalization Note** Positivity of $t_1$ and $t_2$ is required because truthfulness quantifies over positive types only.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 177, Proposition 4.4 (Independence)

import Mathlib
import Definitions.Def_AlgMechDesign_LowerBound_Model

namespace AlgMechDesign.LowerBound

/-- Proposition 4.4 (Independence): for a truthful direct mechanism, two positive type vectors
that agree off agent `i` and give agent `i` the same set of tasks give agent `i` the same
payment. -/
theorem independence {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htruth : IsTruthful alloc pay)
    (t₁ t₂ : Fin n → Fin k → ℝ) (h₁ : IsType t₁) (h₂ : IsType t₂) (i : Fin n)
    (hothers : ∀ j : Fin n, j ≠ i → t₁ j = t₂ j)
    (hx : taskSet (alloc t₁) i = taskSet (alloc t₂) i) :
    pay t₁ i = pay t₂ i := by sorry

end AlgMechDesign.LowerBound
