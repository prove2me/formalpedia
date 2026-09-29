-- Prove2me | Theorems.Thm_AKSSorting_Core_consecutive_violation
-- name    : AKSSorting.Core.consecutive_violation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T10:15:20.097677+00:00
-- url     : https://prove2.me/theorems/e01f5a67-d8e9-4cfc-9df4-3def149ff910
-- title:
--   Lemma 12(a) — a violation of R^β between two nodes is witnessed by consecutive nodes
-- statement:
--   Let $C$ be a chain on level $i$, $G$ a position, $\beta>0$, and $t_1<t_2$ nodes of level $i$ such that $R^\beta_G(t_1,t_2)$ fails. Then there are consecutive nodes $t_1'<t_2'$ of level $i$ with
--   $$ t_1\le t_1'<t_2'\le t_2 \quad\text{and}\quad \neg R^\beta_G(t_1',t_2'). $$
--
--   Out-of-order contents between two distant nodes can be localized to a pair of neighbouring nodes, where the local improvement steps of the algorithm act.
--
--   **Formalization Note** Consecutive means $t_2'=t_1'+1$ in the order of the level (`Fin (2^i)`). A position is an injective map from registers to contents.
-- source:
--   Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983), p. 14, Lemma 12(a); p. 13, Definition 8.1

import Mathlib
import Definitions.Def_AKSSorting_Core_IsChain
import Definitions.Def_AKSSorting_Core_Rbeta

namespace AKSSorting.Core

/-- Lemma 12(a) (Ajtai–Komlós–Szemerédi 1983, p. 14). Let `C` be a chain on level `i`, `G` a
position (an injective assignment of contents to registers), `β > 0`, and `t₁ < t₂` nodes of
`Dom(C)` with `¬R^β_G(t₁, t₂)`. Then there are consecutive nodes `t₁' < t₂'` (`t₂' = t₁' + 1`)
with `t₁ ≤ t₁' < t₂' ≤ t₂` and `¬R^β_G(t₁', t₂')`. -/
theorem consecutive_violation {R : Type} [DecidableEq R] {α : Type} [LinearOrder α] {i : ℕ}
    (C : Fin (2 ^ i) → Finset R) (hC : IsChain C) (G : R → α) (hG : Function.Injective G)
    (β : ℝ) (hβ : 0 < β) (t₁ t₂ : Fin (2 ^ i)) (h12 : t₁ < t₂) (hR : ¬ Rbeta G C β t₁ t₂) :
    ∃ t₁' t₂' : Fin (2 ^ i), t₁'.val + 1 = t₂'.val ∧ t₁ ≤ t₁' ∧ t₂' ≤ t₂ ∧
      ¬ Rbeta G C β t₁' t₂' := by sorry

end AKSSorting.Core
