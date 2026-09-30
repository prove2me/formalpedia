-- Prove2me | Theorems.Thm_AlgMechDesign_Additive_maximization
-- name    : AlgMechDesign.Additive.maximization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T19:14:13.417935+00:00
-- url     : https://prove2.me/theorems/1bf6c5df-d17d-4009-a0f9-e85832e5fddd
-- title:
--   Proposition 4.5 (Maximization) — $x^i(t)$ maximizes $p^i(X,t^{-i}) - t^i(X)$ over attainable $X$
-- statement:
--   Let $m=(x,p)$ be a truthful mechanism for task scheduling, $t$ a positive type vector and $i$ an agent. For a set $X$ of tasks write $t^i(X) = \sum_{j\in X} t^i_j$. Then for every set $X$ that is attainable for agent $i$ against $t^{-i}$ (some positive declaration $t'^i$ gives $x^i(t'^i,t^{-i}) = X$),
--
--   $$p^i(X,t^{-i}) - t^i(X) \;\le\; p^i\bigl(x^i(t),t^{-i}\bigr) - t^i\bigl(x^i(t)\bigr).$$
--
--   That is, the mechanism allocates to agent $i$ a set of tasks maximizing the agent's utility at the offered prices; otherwise the agent would misreport to obtain the better set.
--
--   **Formalization Note** The paper states the maximization over all $X\subseteq\{1,\dots,k\}$. With the price $0$ that Definition 12 assigns to unattainable sets this is false in general (a truthful mechanism may never give agent $i$ the empty set while paying it negative amounts, and then $\emptyset$ with price $0$ would beat $x^i(t)$). The statement here takes the maximum over attainable sets, which is what the paper's proof sketch establishes.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 178, Proposition 4.5 (Maximization), restricted to attainable sets

import Mathlib
import Definitions.Def_AlgMechDesign_Additive_Model
import Definitions.Def_AlgMechDesign_Additive_Price

namespace AlgMechDesign.Additive

open Finset

/-- Proposition 4.5 (Maximization), p. 178, over attainable sets: for a truthful mechanism, a
positive type vector `t` and an agent `i`, the set `xⁱ(t)` maximizes
`pⁱ(X, t⁻ⁱ) - tⁱ(X)` among all sets `X` that agent `i` can obtain against `t⁻ⁱ`. -/
theorem maximization {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htr : IsTruthful alloc pay)
    (t : Fin n → Fin k → ℝ) (ht : IsType t) (i : Fin n) (X : Finset (Fin k))
    (hX : IsAttainable alloc i t X) :
    price alloc pay i X t - ∑ j ∈ X, t i j ≤
      price alloc pay i (taskSet (alloc t) i) t - ∑ j ∈ taskSet (alloc t) i, t i j := by sorry

end AlgMechDesign.Additive
