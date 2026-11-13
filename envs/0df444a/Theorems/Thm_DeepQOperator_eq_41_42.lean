-- Prove2me | Theorems.Thm_DeepQOperator_eq_41_42
-- name    : DeepQOperator.eq_41_42
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:03:25.048688+00:00
-- url     : https://prove2.me/theorems/29a84fdf-4640-471a-a1a5-e5af6664e59f
-- title:
--   (41)–(42): the uniform quantizer has error at most $2^{-d}$
-- statement:
--   For every integer $d\ge1$ and every $x\in[-1,1]$, the index of the uniform encoder (41) satisfies $j_d(x)\in\{0,\dots,2^d-1\}$ and the reconstruction satisfies
--   $$|Q_d(x)-x|\le2^{-d}.\tag{42}$$
--   Moreover each encoder $j_d$ is Borel measurable.
--
--   This is the quantization error used for the five-bit samples and the $v$-bit candidate replies of Theorem 2's protocol, including at the endpoints and at bin boundaries.
--
--   **Formalization Note** $2^{-d}$ is an integer power of $2$ in $\mathbb R$; measurability is from the Borel σ-algebra on $\mathbb R$ to the discrete one on $\mathbb N$.
--
--   Differences from the source:
--   - encoding: j_d(x) ∈ {0, …, 2^d − 1} → jEnc d x : ℕ with jEnc d x < 2^d; reason: the integer floor is nonnegative on [−1, 1]; same values
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix E.1, eqs. (41)–(42), p.23 (PDF p.26)

import Mathlib
import Definitions.Def_DeepQOperator_Quantizer

namespace DeepQOperator

/-- **(41)–(42)** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix E.1, p.23, PDF p.26).

For an integer `d ≥ 1` and `x ∈ [-1, 1]`, the index `j_d(x)` lies in `{0, …, 2^d - 1}`, the
reconstruction obeys `|Q_d(x) - x| ≤ 2^{-d}` (42), and the encoder is Borel measurable.

**Formalization Note.** `jEnc`, `qRound` are (41) (see `Def_DeepQOperator_Quantizer`).
`2^{-d}` is the integer power `(2:ℝ) ^ (-(d:ℤ))`. Measurability is with the Borel σ-algebra on
`ℝ` and the discrete one on `ℕ`. -/
theorem eq_41_42 :
    (∀ d : ℕ, 1 ≤ d → ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      jEnc d x < 2 ^ d ∧ |qRound d x - x| ≤ (2 : ℝ) ^ (-(d : ℤ))) ∧
    (∀ d : ℕ, Measurable (jEnc d)) := by sorry

end DeepQOperator
