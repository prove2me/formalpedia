-- Prove2me | Theorems.Thm_BalancedKneser_theorem_1_1
-- name    : BalancedKneser.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:45:50.902426+00:00
-- url     : https://prove2.me/theorems/c7bd2409-bb8b-4eea-b342-a90a152b9bf0
-- title:
--   Theorem 1.1 (Sharp balanced EF1; EF2 for nine agents)
-- statement:
--   Indivisible goods are divided between two prescribed nonempty groups of agents; every member of a group receives the group's bundle, and each agent has her own monotone valuation. An allocation is **balanced** if the two bundle sizes differ by at most one, and **EF$c$** if every agent stops envying the other bundle after removing at most $c$ goods from it. Then:
--
--   1. for every finite set of goods, every split into groups of sizes $q_1,q_2\ge1$ with $q_1+q_2\le5$, and all monotone valuations, there is a balanced EF1 allocation;
--   2. for every finite set of goods, every split with $q_1,q_2\ge1$ and $q_1+q_2\le9$, and all monotone valuations, there is a balanced EF2 allocation;
--   3. for every split with $q_1,q_2\ge1$ and $q_1+q_2=6$ and every even number $2n\ge4$ of goods, there are monotone valuations taking only the values $0$ and $1$ (and vanishing on the empty bundle) for which no balanced EF1 allocation exists.
--
--   The guarantee for five agents is sharp by clause 3, and the nine-agent EF2 guarantee improves the previous five. The proof combines the chromatic threshold of Theorem 2.1 with $\chi(G_{n,2})=6$ and $\chi(G_{n,3})\ge10$ (Theorem 1.2), together with the small cases and a dummy good for an odd number of goods.
--
--   **Formalization Note** Goods form an arbitrary finite type (any number of goods, including zero and odd numbers); a valuation is any monotone function $\mathrm{Finset}\,M\to\mathbb R$. In clause 3 the goods are $\mathrm{Fin}\,2n$ with $n\ge2$.
--
--   Differences from the source:
--   - generalization: arbitrary monotone valuations (in §2 normalized, u : 2^M → ℝ≥0) → any monotone u : Finset M → ℝ, with no normalization or sign condition; reason: normalized nonnegative valuations are a special case; EFc comparisons are unchanged by adding a constant
--   - generalization: monotone 0/1-valued valuations can prevent balanced EF1 → the counterexample valuations are monotone, {0,1}-valued and also satisfy u ∅ = 0; reason: a stronger counterexample (the one Lemma 2.2 produces); it specializes to the printed clause
--   - encoding: any number of goods; every even number of goods at least four → goods M : Type with Fintype and DecidableEq; Fin (2 * n) with 2 ≤ n; reason: EFc and balance are invariant under relabelling goods; same instances
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, Theorem 1.1, p.1 (PDF p.3); proof p.5 (PDF p.7), Consequences and boundary cases

import Mathlib
import Definitions.Def_BalancedKneser_IsBalancedEF

namespace BalancedKneser

/-- **Theorem 1.1 (Sharp balanced EF1; EF2 for nine agents)** (Alipour–Jafari, *Balanced Fair
Division and Generalized Kneser Graphs*, arXiv:2611.04486v1, p.1 (PDF p.3); proof p.5
(PDF p.7)): "Every instance with at most five agents admits balanced EF1, and every instance
with at most nine agents admits balanced EF2, for arbitrary monotone valuations and every
prescribed split into two nonempty groups. For every split of six agents and every even number
of goods at least four, monotone 0/1-valued valuations can prevent balanced EF1."

1. For every finite set of goods `M`, every split `q₁, q₂ ≥ 1` with `q₁ + q₂ ≤ 5` and all
   monotone valuations, a balanced EF1 allocation exists.
2. The same with `q₁ + q₂ ≤ 9` and EF2.
3. For every split `q₁, q₂ ≥ 1` with `q₁ + q₂ = 6` and every `n ≥ 2`, there are normalized
   monotone `{0,1}`-valued valuations on the `2n` goods `Fin (2n)` with no balanced EF1
   allocation.

Formalization Note: goods are any `Fintype` in `Type` (any number, including 0 and odd); a
valuation is any monotone `Finset M → ℝ`. The counterexample of clause 3 is also normalized
(`u ∅ = 0`), which is stronger than printed. -/
theorem theorem_1_1 :
    (∀ (M : Type) [Fintype M] [DecidableEq M] (q₁ q₂ : ℕ), 1 ≤ q₁ → 1 ≤ q₂ → q₁ + q₂ ≤ 5 →
      ∀ (u₁ : Fin q₁ → Finset M → ℝ) (u₂ : Fin q₂ → Finset M → ℝ),
        (∀ i, Monotone (u₁ i)) → (∀ j, Monotone (u₂ j)) →
        ∃ A : Finset M, IsBalancedEF 1 u₁ u₂ A) ∧
    (∀ (M : Type) [Fintype M] [DecidableEq M] (q₁ q₂ : ℕ), 1 ≤ q₁ → 1 ≤ q₂ → q₁ + q₂ ≤ 9 →
      ∀ (u₁ : Fin q₁ → Finset M → ℝ) (u₂ : Fin q₂ → Finset M → ℝ),
        (∀ i, Monotone (u₁ i)) → (∀ j, Monotone (u₂ j)) →
        ∃ A : Finset M, IsBalancedEF 2 u₁ u₂ A) ∧
    (∀ (n q₁ q₂ : ℕ), 2 ≤ n → 1 ≤ q₁ → 1 ≤ q₂ → q₁ + q₂ = 6 →
      ∃ (u₁ : Fin q₁ → Finset (Fin (2 * n)) → ℝ) (u₂ : Fin q₂ → Finset (Fin (2 * n)) → ℝ),
        (∀ i, Monotone (u₁ i) ∧ u₁ i ∅ = 0 ∧ ∀ S, u₁ i S = 0 ∨ u₁ i S = 1) ∧
        (∀ j, Monotone (u₂ j) ∧ u₂ j ∅ = 0 ∧ ∀ S, u₂ j S = 0 ∨ u₂ j S = 1) ∧
        ¬ ∃ A : Finset (Fin (2 * n)), IsBalancedEF 1 u₁ u₂ A) := by sorry

end BalancedKneser
