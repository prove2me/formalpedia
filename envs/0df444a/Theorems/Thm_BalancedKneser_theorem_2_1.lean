-- Prove2me | Theorems.Thm_BalancedKneser_theorem_2_1
-- name    : BalancedKneser.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:45:54.954307+00:00
-- url     : https://prove2.me/theorems/f2b45c35-2c48-42ce-8974-e2bec2302543
-- title:
--   Theorem 2.1 (The balanced threshold) — balanced EF$c$ for every profile iff $q_1+q_2<\chi(G_{n,c+1})$
-- statement:
--   Let $n>c\ge1$ and $q_1,q_2\ge1$. Divide $2n$ goods between a first group of $q_1$ agents and a second group of $q_2$ agents, each agent having a normalized monotone valuation ($u(\emptyset)=0$, $u(S)\le u(T)$ for $S\subseteq T$). Then:
--
--   1. every such profile admits a balanced EF$c$ allocation for this split if and only if
--   $$
--   q_1+q_2<\chi(G_{n,c+1});
--   $$
--   2. if $q_1+q_2\ge\chi(G_{n,c+1})$, there is a profile of normalized monotone valuations taking only the values $0$ and $1$ that admits no balanced EF$c$ allocation.
--
--   Here $G_{n,c+1}=KG(2n,n,c+1)$ and $\chi$ is its chromatic number. Combined with $\chi(G_{n,2})=6$ and $\chi(G_{n,3})\ge10$ (Theorem 1.2), this yields the existence and the sharpness parts of Theorem 1.1 for an even number of goods.
--
--   **Formalization Note** $\chi$ is Mathlib's `SimpleGraph.chromaticNumber`, valued in $\mathbb N\cup\{\infty\}$; balanced on $2n$ goods means $|A|=n$.
--
--   Differences from the source:
--   - encoding: normalized monotone valuations u : 2^M → ℝ≥0 → u : Finset (Fin (2n)) → ℝ with Monotone u and u ∅ = 0; reason: monotone with u(∅) = 0 forces u ≥ 0; same valuations
--   - encoding: χ(G_{n,c+1}), a natural number → SimpleGraph.chromaticNumber in ℕ∞, compared with ((q₁ + q₂ : ℕ) : ℕ∞); reason: G_{n,c+1} is finite, so χ is finite; same comparisons
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, Theorem 2.1, p.3 (PDF p.5); proof p.4 (PDF p.6)

import Mathlib
import Definitions.Def_BalancedKneser_KG
import Definitions.Def_BalancedKneser_IsBalancedEF

namespace BalancedKneser

/-- **Theorem 2.1 (The balanced threshold)** (Alipour–Jafari, arXiv:2611.04486v1, p.3
(PDF p.5); proof p.4): "Let n > c ≥ 1 and q1, q2 ≥ 1. Every profile of normalized monotone
valuations admits a balanced EFc allocation for this split if and only if q1 + q2 < χ(G_{n,c+1}).
If the inequality fails, a counterexample exists with 0/1-valued valuations."

Goods are `M = [2n]` (`Fin (2 * n)`); a normalized monotone valuation is a monotone
`u : Finset M → ℝ` with `u ∅ = 0` (hence `u ≥ 0`). The first group has `q₁` agents, the second
`q₂`.

Formalization Note: `χ` is Mathlib's `SimpleGraph.chromaticNumber : ℕ∞`; balanced on `2n` goods
(`IsBalanced`, sizes differing by at most one) means `|A| = n`. -/
theorem theorem_2_1 (n c q₁ q₂ : ℕ) (hc : 1 ≤ c) (hcn : c < n) (hq₁ : 1 ≤ q₁) (hq₂ : 1 ≤ q₂) :
    ((∀ (u₁ : Fin q₁ → Finset (Fin (2 * n)) → ℝ) (u₂ : Fin q₂ → Finset (Fin (2 * n)) → ℝ),
        (∀ i, Monotone (u₁ i) ∧ u₁ i ∅ = 0) → (∀ j, Monotone (u₂ j) ∧ u₂ j ∅ = 0) →
        ∃ A : Finset (Fin (2 * n)), IsBalancedEF c u₁ u₂ A) ↔
      ((q₁ + q₂ : ℕ) : ℕ∞) < (Gnr n (c + 1)).chromaticNumber) ∧
    (¬ ((q₁ + q₂ : ℕ) : ℕ∞) < (Gnr n (c + 1)).chromaticNumber →
      ∃ (u₁ : Fin q₁ → Finset (Fin (2 * n)) → ℝ) (u₂ : Fin q₂ → Finset (Fin (2 * n)) → ℝ),
        (∀ i, Monotone (u₁ i) ∧ u₁ i ∅ = 0 ∧ ∀ S, u₁ i S = 0 ∨ u₁ i S = 1) ∧
        (∀ j, Monotone (u₂ j) ∧ u₂ j ∅ = 0 ∧ ∀ S, u₂ j S = 0 ∨ u₂ j S = 1) ∧
        ¬ ∃ A : Finset (Fin (2 * n)), IsBalancedEF c u₁ u₂ A) := by sorry

end BalancedKneser
