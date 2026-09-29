-- Prove2me | Theorems.Thm_ClassicalSchur_le_erL_of_groupPartition
-- name    : ClassicalSchur.le_erL_of_groupPartition
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-26T21:24:23.930749+00:00
-- url     : https://prove2.me/theorems/b470a319-51e7-4658-9373-3027e96d2b77
-- title:
--   $L(n) \ge m_1 m_2$ when $\mathbb{Z}_{m_1} \times \mathbb{Z}_{m_2} \setminus \{0\}$ is covered by $n - 1$ sets sumfree in the group
-- statement:
--   This is Corollary 4 of the note: a lower bound for $L(n)$ from a finite abelian group.
--
--   Let $n \ge 3$ and $m_1, m_2 \ge 1$ be natural numbers, and let $G = \mathbb{Z}_{m_1} \times \mathbb{Z}_{m_2}$. Suppose that $C_1, \dots, C_{n-1} \subseteq G$ are sumfree in $G$ ($x + y \notin C_i$ for all $x, y \in C_i$, including $x = y$) and that every nonzero element of $G$ lies in at least one $C_i$. Then
--
--   $$
--   L(n) \ge m_1 m_2 ,
--   $$
--
--   where $L(n)$ is the least positive integer $L$ such that every sequence $A$ of positive integers with $|A| = L$ and average $\mu(A) \le n$ satisfies $\operatorname{sdeg}(\hat A) \ge n$ (Definition 5.1 of Eliahou and Revuelta).
--
--   With $n = 5$, $m_1 = m_2 = 7$ and the four sets $D_0, \dots, D_3$ of the Values bundle, it gives $L(5) \ge 49$. For comparison, the lower bound of Proposition 5.3 of the paper at $n = 5$ is $S(4) + 1 = 45$, where $S(4) = 44$ is the Schur number.
--
--   **Formalization Note** The note assumes that $C_1, \dots, C_{n-1}$ partition $G \setminus \{0\}$; the Lean statement only asks that they cover the nonzero elements, a weaker hypothesis. The conditions $m_1, m_2 \ge 1$, which the note takes from Lemma 3, are explicit hypotheses. $L(n)$ is `erL n` of the Basic bundle.
-- source:
--   A. McKenna, "The Schur degree of block sums: L(4) = 16 and L(5) ≥ 49", Zenodo (2026), https://doi.org/10.5281/zenodo.22987189, §4, Corollary 4.2. Lean source: https://github.com/mysticflounder/schur-degree-block-sums/blob/v1.0.1/lean/ClassicalSchur/Lift.lean#L186-L209 (release v1.0.1, doi:10.5281/zenodo.22987688).

import Definitions.Def_ClassicalSchurBasic
import Definitions.Def_ClassicalSchurLift
import Definitions.Def_ClassicalSchurRamsey
import Mathlib

open ClassicalSchur

theorem ClassicalSchur.le_erL_of_groupPartition {n m₁ m₂ : ℕ} (hn : 3 ≤ n) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (C : Fin (n - 1) → Set (ZMod m₁ × ZMod m₂)) (hC : ∀ i, GroupSumFree (C i))
    (hcov : ∀ g : ZMod m₁ × ZMod m₂, g ≠ 0 → ∃ i, g ∈ C i) : m₁ * m₂ ≤ erL n := by sorry
