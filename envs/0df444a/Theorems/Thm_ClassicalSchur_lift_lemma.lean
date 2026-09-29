-- Prove2me | Theorems.Thm_ClassicalSchur_lift_lemma
-- name    : ClassicalSchur.lift_lemma
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-26T21:23:55.58888+00:00
-- url     : https://prove2.me/theorems/fb4530dc-ebd1-429b-a44b-b694190be4d1
-- title:
--   Lift lemma: a sumfree $q$-cover of $\mathbb{Z}_{m_1} \times \mathbb{Z}_{m_2} \setminus \{0\}$ gives a positive sequence of length $m_1 m_2 - 1$ with $\operatorname{sdeg}(\hat A) \le q$
-- statement:
--   This is Lemma 3 of the note: a lift from the finite abelian group $\mathbb{Z}_{m_1} \times \mathbb{Z}_{m_2}$ to sequences of positive integers.
--
--   Let $m_1, m_2, q \ge 1$ be natural numbers, let $G = \mathbb{Z}_{m_1} \times \mathbb{Z}_{m_2}$, and let $M \ge 3m_1 - 2$. Suppose that $C_1, \dots, C_q \subseteq G$ are sumfree in $G$ ($x + y \notin C_i$ for all $x, y \in C_i$, including $x = y$) and that every nonzero element of $G$ lies in at least one $C_i$. Let $A = (a_1, a_2, \dots)$ be the lifted sequence of the Lift bundle, that is, the sequence of successive jumps of the grid $X = \{u + Mj : 0 \le u \le m_1 - 1,\ 0 \le j \le m_2 - 1\}$. Let $\hat A$ be the set of block sums of $A$, and $\operatorname{sdeg}$ the Schur degree. Then
--
--   $$
--   \operatorname{sdeg}(\hat A) \le q ,
--   $$
--
--   and in full the statement has four parts:
--
--   1. $A$ has length $|A| = m_1 m_2 - 1$;
--   2. every entry of $A$ is positive;
--   3. $\operatorname{sdeg}(\hat A) \le q$;
--   4. for every $L$ with $0 \le L \le m_1 m_2 - 1$, the first $L$ entries of $A$ have sum $a_1 + \dots + a_L = (L \bmod m_1) + M \lfloor L/m_1 \rfloor$.
--
--   The lemma turns a cover of $G \setminus \{0\}$ by sets sumfree in $G$ into a sequence for the property of Definition 5.1 of Eliahou and Revuelta: with $M = 3m_1 - 2$, part 4 bounds the average of every nonempty prefix of $A$ by $3$, and part 3 bounds the Schur degree of its block sums. These are the facts behind the lower bound $L(n) \ge m_1 m_2$ (Corollary 4 of the note).
--
--   **Formalization Note** The Lean statement differs from the note in three places. (1) The note assumes that the $C_i$ partition $G \setminus \{0\}$; here they only need to cover the nonzero elements, a weaker hypothesis. (2) The note bounds the prefix sums by $L \cdot \max(1, M/m_1)$ for $1 \le L \le m_1 m_2 - 1$; part 4 gives their exact value, which implies that bound, and it includes $L = 0$. (3) Part 2 is implicit in the note, where $A$ is the jump sequence of a set. The hypothesis $q \ge 1$ is also in the note: for $q = 0$ the statement fails at $m_1 = m_2 = 1$, where $A$ is empty, $\hat A = \emptyset$ and $\operatorname{sdeg}(\emptyset) = 1$.
-- source:
--   A. McKenna, "The Schur degree of block sums: L(4) = 16 and L(5) ≥ 49", Zenodo (2026), https://doi.org/10.5281/zenodo.22987189, §4, Lemma 4.1, and §7 (Lemma 4.1 with the sequence given by its prefix sums x_L). Lean source: https://github.com/mysticflounder/schur-degree-block-sums/blob/v1.0.1/lean/ClassicalSchur/Lift.lean#L174-L184 (release v1.0.1, doi:10.5281/zenodo.22987688).

import Definitions.Def_ClassicalSchurBasic
import Definitions.Def_ClassicalSchurLift
import Mathlib

open ClassicalSchur

theorem ClassicalSchur.lift_lemma {m₁ m₂ q M : ℕ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hq : 0 < q)
    (hM : 3 * m₁ - 2 ≤ M) (C : Fin q → Set (ZMod m₁ × ZMod m₂))
    (hC : ∀ i, GroupSumFree (C i)) (hcov : ∀ g : ZMod m₁ × ZMod m₂, g ≠ 0 → ∃ i, g ∈ C i) :
    (liftSeq m₁ m₂ M).length = m₁ * m₂ - 1 ∧ (∀ a ∈ liftSeq m₁ m₂ M, 0 < a) ∧
      sdeg (blockSums (liftSeq m₁ m₂ M)) ≤ q ∧
      ∀ L ≤ m₁ * m₂ - 1, ((liftSeq m₁ m₂ M).take L).sum = L % m₁ + M * (L / m₁) := by sorry
