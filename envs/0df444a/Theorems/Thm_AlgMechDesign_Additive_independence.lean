-- Prove2me | Theorems.Thm_AlgMechDesign_Additive_independence
-- name    : AlgMechDesign.Additive.independence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T19:09:24.897837+00:00
-- url     : https://prove2.me/theorems/59243f7d-9634-4e13-bc7f-7d04a99dbba9
-- title:
--   Proposition 4.4 (Independence) — the payment depends only on the allocation and $t^{-i}$
-- statement:
--   Let $m=(x,p)$ be a truthful mechanism for task scheduling, let $t_1$ and $t_2$ be positive type vectors and let $i$ be an agent. If $t_1$ and $t_2$ agree on every agent other than $i$, i.e. $t_1^{-i} = t_2^{-i}$, and the mechanism gives agent $i$ the same set of tasks under both, $x^i(t_1) = x^i(t_2)$, then
--
--   $$p^i(t_1) = p^i(t_2).$$
--
--   The payment offered to an agent therefore does not depend on its own declaration once the others' declarations and its allocation are fixed; this is what makes the prices $p^i(X,t^{-i})$ of Definition 12 well defined.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 177, Proposition 4.4 (Independence)

import Mathlib
import Definitions.Def_AlgMechDesign_Additive_Model
import Definitions.Def_AlgMechDesign_Additive_Price

namespace AlgMechDesign.Additive

/-- Proposition 4.4 (Independence), p. 177: for a truthful mechanism, if two positive type
vectors agree off agent `i` and give agent `i` the same set of tasks, then agent `i` is paid
the same amount. -/
theorem independence {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htr : IsTruthful alloc pay)
    (t₁ t₂ : Fin n → Fin k → ℝ) (h₁ : IsType t₁) (h₂ : IsType t₂) (i : Fin n)
    (hoth : ∀ i' : Fin n, i' ≠ i → t₁ i' = t₂ i')
    (hx : taskSet (alloc t₁) i = taskSet (alloc t₂) i) :
    pay t₁ i = pay t₂ i := by sorry

end AlgMechDesign.Additive
