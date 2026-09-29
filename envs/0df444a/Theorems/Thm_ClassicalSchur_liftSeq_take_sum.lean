-- Prove2me | Theorems.Thm_ClassicalSchur_liftSeq_take_sum
-- name    : ClassicalSchur.liftSeq_take_sum
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-26T21:23:02.685516+00:00
-- url     : https://prove2.me/theorems/919b12ec-50cd-4c45-bcc3-1c00b72eda27
-- title:
--   Prefix sums of the lifted sequence: the first $L$ entries sum to $(L \bmod m_1) + M\lfloor L/m_1 \rfloor$
-- statement:
--   This lemma computes the prefix sums of the lifted sequence exactly.
--
--   Let $m_1 \ge 1$, $m_2$ and $M \ge m_1$ be natural numbers, and let $x_L = (L \bmod m_1) + M \lfloor L/m_1 \rfloor$ for $L \in \mathbb{N}$. Let $A = (a_1, \dots, a_{m_1 m_2 - 1})$ be the lifted sequence of the Lift bundle, with $a_i = x_i - x_{i-1}$; it is the sequence of jumps of the grid $X = \{u + Mj : 0 \le u \le m_1 - 1,\ 0 \le j \le m_2 - 1\}$. Then for every $L$ with $0 \le L \le m_1 m_2 - 1$, the sum of the first $L$ entries of $A$ is
--
--   $$
--   a_1 + a_2 + \dots + a_L = (L \bmod m_1) + M \left\lfloor \frac{L}{m_1} \right\rfloor = x_L .
--   $$
--
--   For $L = 0$ both sides are $0$.
--
--   The formula identifies the prefix sums of $A$ with the elements of the grid $X$. It is the fourth part of the lift lemma, and it gives the bound on the prefix averages of $A$ that the lower bound $L(n) \ge m_1 m_2$ needs.
--
--   **Formalization Note** "The first $L$ entries" is `List.take L`, and $m_1 m_2 - 1$ is truncated subtraction on $\mathbb{N}$. There is no hypothesis on $m_2$; for $m_2 = 0$ only $L = 0$ is allowed.
-- source:
--   A. McKenna, "The Schur degree of block sums: L(4) = 16 and L(5) ≥ 49", Zenodo (2026), https://doi.org/10.5281/zenodo.22987189, §4, proof of Lemma 4.1 (the first L entries of A have sum x_L). Lean source: https://github.com/mysticflounder/schur-degree-block-sums/blob/v1.0.1/lean/ClassicalSchur/Lift.lean#L64-L77 (release v1.0.1, doi:10.5281/zenodo.22987688).

import Definitions.Def_ClassicalSchurLift
import Mathlib

open ClassicalSchur

theorem ClassicalSchur.liftSeq_take_sum {m₁ m₂ M : ℕ} (hm₁ : 0 < m₁) (hM : m₁ ≤ M) {L : ℕ}
    (hL : L ≤ m₁ * m₂ - 1) : ((liftSeq m₁ m₂ M).take L).sum = liftPrefix m₁ M L := by sorry
