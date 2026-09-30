-- Prove2me | Theorems.Thm_AlgMechDesign_MinWork_minwork_is_vgc
-- name    : AlgMechDesign.MinWork.minwork_is_vgc
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T18:14:09.22998+00:00
-- url     : https://prove2.me/theorems/85a4c406-fb0c-47d1-a161-6ab656630164
-- title:
--   MinWork belongs to the VGC family (proof of Claim 4.2)
-- statement:
--   Let $n \ge 2$ agents and $k$ tasks be given, let $x(\cdot)$ be any MinWork allocation rule (every task goes to an agent with minimal declared time, ties broken arbitrarily), and let $t$ be a positive type vector. Then:
--
--   1. $x(t)$ maximizes the utilitarian function over all allocations $y$:
--   $$
--   \sum_{i=1}^n v^i(t^i, y) \le \sum_{i=1}^n v^i(t^i, x(t)), \qquad v^i(t^i, y) = -\sum_{j \in y^i} t^i_j .
--   $$
--   2. For every agent $i$ the MinWork payment has the Groves form
--   $$
--   p^i(t) = \sum_{i' \neq i} v^{i'}\big(t^{i'}, x(t)\big) + h^{-i}(t), \qquad h^{-i}(t) = \sum_{j=1}^k \min_{i' \neq i} t^{i'}_j .
--   $$
--   3. $h^{-i}$ depends only on $t^{-i}$: replacing $t^i$ by any other vector leaves it unchanged.
--
--   Together these say MinWork is a VGC mechanism (Definition 7), so by Groves' theorem (Theorem 3.1) it is truthful.
--
--   **Formalization Note** Part 3 makes explicit the paper's requirement that $h^i$ be "an arbitrary function of $t^{-i}$".
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 177, proof of Claim 4.2, first paragraph (with Definition 7, p. 173)

import Mathlib
import Definitions.Def_AlgMechDesign_MinWork_Model
import Definitions.Def_AlgMechDesign_MinWork_Mechanism

namespace AlgMechDesign.MinWork

open Finset

/-- MinWork belongs to the VGC family (proof of Claim 4.2): its allocation maximizes the
utilitarian function `∑ᵢ vⁱ(tⁱ, x) = -∑ᵢ tⁱ(xⁱ)` over all allocations, and its payment to
agent `i` equals `∑_{i' ≠ i} v^{i'}(t^{i'}, x(t)) + h^{-i}(t)` with
`h^{-i}(t) = ∑_j min_{i' ≠ i} t^{i'}_j`, a quantity that does not depend on `tⁱ`. -/
theorem minwork_is_vgc {n k : ℕ} (hn : 2 ≤ n)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (hmin : IsMinWorkAlloc alloc)
    (t : Fin n → Fin k → ℝ) (ht : IsType t) :
    (∀ x : Fin k → Fin n, ∑ i, -(load t x i) ≤ ∑ i, -(load t (alloc t) i)) ∧
    (∀ i : Fin n,
      minWorkPay hn alloc t i =
        ∑ i' ∈ univ.erase i, -(load t (alloc t) i') + ∑ j, secondBest hn t i j) ∧
    (∀ (i : Fin n) (ti' : Fin k → ℝ),
      ∑ j, secondBest hn (Function.update t i ti') i j = ∑ j, secondBest hn t i j) := by sorry

end AlgMechDesign.MinWork
