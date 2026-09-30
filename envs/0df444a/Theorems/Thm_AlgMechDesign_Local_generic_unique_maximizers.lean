-- Prove2me | Theorems.Thm_AlgMechDesign_Local_generic_unique_maximizers
-- name    : AlgMechDesign.Local.generic_unique_maximizers
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T19:49:52.879654+00:00
-- url     : https://prove2.me/theorems/1bf511a1-c423-4182-91d3-1c33908ea1df
-- title:
--   Lemma 4.13 — nearby type vectors at which every agent's utility maximizer is unique
-- statement:
--   Let $(x, p)$ be a truthful mechanism for task scheduling. For every positive type vector $t$ and every $\varepsilon > 0$ there is a positive type vector $t'$ with
--   $$
--   \|t - t'\|_\infty = \max_{i, j} |t^i_j - t'^i_j| < \varepsilon
--   $$
--   such that, for every agent $i$, the set $x^i(t')$ is the unique maximizer of $i$'s utility $p^i(X, t'^{-i}) - t'^i(X)$ among the sets $X$ attainable against $t'^{-i}$.
--
--   The lemma turns the weak inequalities of Lemma 4.7 into strict ones at a type vector arbitrarily close to any given one; the lower-bound argument for local mechanisms starts from such a type vector.
--
--   **Formalization Note** $\|\cdot\|$ is Mathlib's norm on `Fin n → Fin k → ℝ`, the sup norm over agents and tasks. The mechanism is arbitrary: no measurability of the allocation or payment functions is assumed.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 180, Lemma 4.13

import Mathlib
import Definitions.Def_AlgMechDesign_Local_Model
import Definitions.Def_AlgMechDesign_Local_Prices

namespace AlgMechDesign.Local

/-- Lemma 4.13, p. 180: for a truthful mechanism, every positive type vector `t` and every
`ε > 0` there is a positive type vector `t'` with `‖t − t'‖ < ε` (sup norm) at which, for every
agent `i`, `xⁱ(t')` is the unique maximizer of `i`'s utility among the attainable sets. -/
theorem generic_unique_maximizers {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htr : IsTruthful alloc pay)
    (t : Fin n → Fin k → ℝ) (ht : IsType t) (ε : ℝ) (hε : 0 < ε) :
    ∃ t' : Fin n → Fin k → ℝ, IsType t' ∧ ‖t - t'‖ < ε ∧
      ∀ i : Fin n, IsUniqueMaximizer alloc pay t' i := by sorry

end AlgMechDesign.Local
