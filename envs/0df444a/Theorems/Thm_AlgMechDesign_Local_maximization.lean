-- Prove2me | Theorems.Thm_AlgMechDesign_Local_maximization
-- name    : AlgMechDesign.Local.maximization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T19:43:48.799273+00:00
-- url     : https://prove2.me/theorems/deec3b41-0d2c-4900-888e-d0d4804440d7
-- title:
--   Proposition 4.5 (Maximization) — each agent receives a utility-maximizing attainable set
-- statement:
--   Let $(x, p)$ be a truthful mechanism for task scheduling, $t$ a positive type vector and $i$ an agent. Then the set $x^i(t)$ allocated to $i$ is attainable against $t^{-i}$, and it maximizes $i$'s utility among all sets attainable against $t^{-i}$:
--   $$
--   x^i(t) \in \arg\max_{X \text{ attainable against } t^{-i}} \bigl(p^i(X, t^{-i}) - t^i(X)\bigr),
--   $$
--   where $p^i(X, t^{-i})$ is the price of Definition 12 and $t^i(X) = \sum_{j \in X} t^i_j$.
--
--   The mechanism thus does for each agent what the agent would do for itself: pick the most profitable set on offer.
--
--   **Formalization Note** The paper takes the arg max over all $X \subseteq \{1,\dots,k\}$. That is false for a truthful mechanism that never leaves agent $i$ without tasks and pays it negative amounts: Definition 12 prices the unattainable empty set at $0$, which then beats $x^i(t)$. The statement here takes the arg max over the attainable sets, which is what the paper's proof sketch establishes.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 178, Proposition 4.5

import Mathlib
import Definitions.Def_AlgMechDesign_Local_Model
import Definitions.Def_AlgMechDesign_Local_Prices

namespace AlgMechDesign.Local

/-- Proposition 4.5 (Maximization), p. 178, over the attainable sets: for a truthful mechanism,
at every positive type vector `t` the set `xⁱ(t)` is attainable and maximizes agent `i`'s
utility `pⁱ(X, t⁻ⁱ) − tⁱ(X)` among all sets `X` attainable against `t⁻ⁱ`. -/
theorem maximization {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htr : IsTruthful alloc pay)
    (t : Fin n → Fin k → ℝ) (ht : IsType t) (i : Fin n) :
    IsAttainable alloc i (agentSet alloc t i) t ∧
      ∀ X : Finset (Fin k), IsAttainable alloc i X t →
        setUtility alloc pay i X t ≤ setUtility alloc pay i (agentSet alloc t i) t := by sorry

end AlgMechDesign.Local
