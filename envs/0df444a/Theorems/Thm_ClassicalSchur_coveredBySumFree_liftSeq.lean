-- Prove2me | Theorems.Thm_ClassicalSchur_coveredBySumFree_liftSeq
-- name    : ClassicalSchur.coveredBySumFree_liftSeq
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-26T21:23:33.242277+00:00
-- url     : https://prove2.me/theorems/c7045059-6ae7-4b72-b3e5-b6b97f9dc538
-- title:
--   A cover of $\mathbb{Z}_{m_1} \times \mathbb{Z}_{m_2} \setminus \{0\}$ by $q$ sets sumfree in the group lifts to a cover of $\hat A$ by $q$ sumfree sets
-- statement:
--   This lemma transfers a cover of a finite abelian group by sumfree sets to a cover of a block-sum set of integers. It is the cover part of Lemma 3 of the note.
--
--   Let $m_1, m_2 \ge 1$ and $q$ be natural numbers, let $G = \mathbb{Z}_{m_1} \times \mathbb{Z}_{m_2}$, and let $M \ge 3m_1 - 2$. Let $A$ be the lifted sequence of the Lift bundle, that is, the sequence of successive jumps of the grid $X = \{u + Mj : 0 \le u \le m_1 - 1,\ 0 \le j \le m_2 - 1\}$, and let $\hat A$ be its set of block sums. Suppose that $C_1, \dots, C_q \subseteq G$ are sumfree in $G$ ($x + y \notin C_i$ for all $x, y \in C_i$, including $x = y$) and that every nonzero element of $G$ lies in at least one $C_i$. Then $\hat A$ is covered by $q$ sumfree sets of natural numbers:
--
--   $$
--   \hat A \subseteq C'_1 \cup \dots \cup C'_q \qquad \text{for some sumfree sets } C'_1, \dots, C'_q \subseteq \mathbb{N}.
--   $$
--
--   This is the step from the group to the integers. It gives the Schur-degree bound $\operatorname{sdeg}(\hat A) \le q$ of the lift lemma, and it is used in the lower bound $L(n) \ge m_1 m_2$.
--
--   **Formalization Note** The note assumes that $C_1, \dots, C_q$ partition $G \setminus \{0\}$; the Lean statement only asks that they cover the nonzero elements, which is a weaker hypothesis (a set that is sumfree in $G$ cannot contain $0$). The case $q = 0$ is allowed.
-- source:
--   A. McKenna, "The Schur degree of block sums: L(4) = 16 and L(5) ≥ 49", Zenodo (2026), https://doi.org/10.5281/zenodo.22987189, §4, Lemma 4.1 (the sumfree q-colouring of Â). Lean source: https://github.com/mysticflounder/schur-degree-block-sums/blob/v1.0.1/lean/ClassicalSchur/Lift.lean#L90-L172 (release v1.0.1, doi:10.5281/zenodo.22987688).

import Definitions.Def_ClassicalSchurBasic
import Definitions.Def_ClassicalSchurLift
import Mathlib

open ClassicalSchur

theorem ClassicalSchur.coveredBySumFree_liftSeq {m₁ m₂ q M : ℕ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hM : 3 * m₁ - 2 ≤ M) (C : Fin q → Set (ZMod m₁ × ZMod m₂))
    (hC : ∀ i, GroupSumFree (C i)) (hcov : ∀ g : ZMod m₁ × ZMod m₂, g ≠ 0 → ∃ i, g ∈ C i) :
    CoveredBySumFree (blockSums (liftSeq m₁ m₂ M)) q := by sorry
