-- Prove2me | Theorems.Thm_AlgMechDesign_LowerBound_maximization
-- name    : AlgMechDesign.LowerBound.maximization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T18:47:49.865988+00:00
-- url     : https://prove2.me/theorems/569ead5a-5253-4a45-ad8a-6d0b813f8637
-- title:
--   Proposition 4.5 (Maximization) — the allocated set maximizes price minus cost over attainable sets
-- statement:
--   Let $(x,p)$ be a truthful direct mechanism for task scheduling, $t$ a positive type vector and $i$ an agent. For a set $X$ of tasks write $t^i(X) = \sum_{j\in X} t^i_j$ and let $p^i(X,t^{-i})$ be the price of Definition 12. Then $x^i(t)$ is itself attainable for $i$ against $t^{-i}$, and it maximizes agent $i$'s benefit among all attainable sets:
--
--   $$
--   x^i(t) \in \operatorname*{arg\,max}_{X \text{ attainable for } i \text{ against } t^{-i}} \big(p^i(X,t^{-i}) - t^i(X)\big).
--   $$
--
--   In words, a truthful mechanism gives each agent the bundle it would have chosen itself at the offered prices; this is the tool for pinning down allocations in the proof of Theorem 4.6.
--
--   **Formalization Note** The paper prints the arg max over all $X \subseteq \{1,\dots,k\}$. With Definition 12's price $0$ for unattainable sets, that version fails for a truthful mechanism that never gives agent $i$ the empty set and pays it a negative amount: the unattainable $\emptyset$ would have benefit $0$, above the attained one. The proof sketch ("otherwise the agent will ... cheat to get the maximum benefit") establishes the maximum over attainable sets, which is what is stated here.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 178, Proposition 4.5 (Maximization) and the Notation before it

import Mathlib
import Definitions.Def_AlgMechDesign_LowerBound_Model
import Definitions.Def_AlgMechDesign_LowerBound_Price

namespace AlgMechDesign.LowerBound

/-- Proposition 4.5 (Maximization), over attainable sets: for a truthful direct mechanism, a
positive type vector `t` and an agent `i`, the set `xⁱ(t)` is attainable and maximizes
`pⁱ(X, t⁻ⁱ) - tⁱ(X)` over all sets `X` attainable for `i` against `t⁻ⁱ`. -/
theorem maximization {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htruth : IsTruthful alloc pay)
    (t : Fin n → Fin k → ℝ) (ht : IsType t) (i : Fin n) :
    IsAttainable alloc i t (taskSet (alloc t) i) ∧
      ∀ X : Finset (Fin k), IsAttainable alloc i t X →
        price alloc pay i X t - taskTime (t i) X ≤
          price alloc pay i (taskSet (alloc t) i) t - taskTime (t i) (taskSet (alloc t) i) := by sorry

end AlgMechDesign.LowerBound
