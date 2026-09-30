-- Prove2me | Theorems.Thm_AlgMechDesign_Local_independence
-- name    : AlgMechDesign.Local.independence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T19:39:23.861153+00:00
-- url     : https://prove2.me/theorems/aec8764c-b680-4c95-871b-502d6a6e831f
-- title:
--   Proposition 4.4 (Independence) — the payment depends only on the allocated set and the others' types
-- statement:
--   Let $(x, p)$ be a truthful mechanism for task scheduling, let $t_1$ and $t_2$ be positive type vectors and let $i$ be an agent. If the two type vectors agree on every agent other than $i$ and give agent $i$ the same set of tasks,
--   $$
--   t_1^{-i} = t_2^{-i}, \quad x^i(t_1) = x^i(t_2) \quad\Longrightarrow\quad p^i(t_1) = p^i(t_2).
--   $$
--
--   The payment offered to an agent therefore does not depend on its own declaration once the others' declarations and its allocated set are fixed. This is what makes the price $p^i(X, t^{-i})$ of Definition 12 well defined.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 177, Proposition 4.4

import Mathlib
import Definitions.Def_AlgMechDesign_Local_Model
import Definitions.Def_AlgMechDesign_Local_Prices

namespace AlgMechDesign.Local

/-- Proposition 4.4 (Independence), p. 177: for a truthful mechanism, if two positive type
vectors agree off agent `i` and give agent `i` the same set of tasks, they give agent `i` the
same payment. -/
theorem independence {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htr : IsTruthful alloc pay)
    (t₁ t₂ : Fin n → Fin k → ℝ) (h₁ : IsType t₁) (h₂ : IsType t₂) (i : Fin n)
    (hothers : ∀ l, l ≠ i → t₁ l = t₂ l) (hx : agentSet alloc t₁ i = agentSet alloc t₂ i) :
    pay t₁ i = pay t₂ i := by sorry

end AlgMechDesign.Local
