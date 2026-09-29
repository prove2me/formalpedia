-- Prove2me | Theorems.Thm_DiophantinePreprocessing_FrankTardos_decomposition_exists
-- name    : DiophantinePreprocessing.FrankTardos.decomposition_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:40:58.414624+00:00
-- url     : https://prove2.me/theorems/7d0c767b-dd57-40b7-ae9f-3972e10d8805
-- title:
--   Theorem 3.1 — decomposition of $w$ into small integer vectors with fast-decreasing coefficients
-- statement:
--   For every vector $w \in \mathbb{R}^n$ and every positive integer $N$ there exist $k \le n$, integer vectors $v_1, \dots, v_k \in \mathbb{Z}^n$ and positive reals $\lambda_1, \dots, \lambda_k$ such that
--
--   1. $$w = \sum_{i=1}^k \lambda_i v_i,$$
--   2. $\|v_i\|_\infty \le N^n$ for $i = 1, \dots, k$, and
--   3. condition (iii) holds: for $i = 2, \dots, k$, $v_i \ne 0$ and $\lambda_i / \lambda_{i-1} \le 1/(N\|v_i\|_\infty)$.
--
--   The theorem expresses an arbitrary real vector as a positive combination of at most $n$ small integer vectors whose coefficients decrease very quickly. It is the structural result on which the preprocessing algorithm is built.
--
--   **Formalization Note** The empty decomposition $k = 0$ is allowed (it represents $w = 0$). Indices run over $\{1, \dots, k\} \subseteq \mathbb{N}$; $v$ and $\lambda$ are functions on $\mathbb{N}$ whose values outside this range are irrelevant. Condition (iii) is the definition `CondIII`, which includes $v_i \ne 0$ for $i \ge 2$.
-- source:
--   Frank & Tardos, An application of simultaneous diophantine approximation in combinatorial optimization, Combinatorica 7(1) (1987), p. 53, Theorem 3.1

import Mathlib
import Definitions.Def_DiophantinePreprocessing_FrankTardos_CondIII

namespace DiophantinePreprocessing.FrankTardos

/-- Frank–Tardos, Theorem 3.1 (p. 53): every `w ∈ ℝⁿ` is `∑_{i=1}^k λ_i v_i` with `k ≤ n`,
`λ_i > 0`, integer `v_i` with `‖v_i‖∞ ≤ Nⁿ`, and condition (iii). -/
theorem decomposition_exists (n N : ℕ) (hN : 0 < N) (w : Fin n → ℝ) :
    ∃ (k : ℕ) (v : ℕ → Fin n → ℤ) (lam : ℕ → ℝ), k ≤ n ∧
      (∀ i ∈ Finset.Icc 1 k, 0 < lam i) ∧
      (∀ j, w j = ∑ i ∈ Finset.Icc 1 k, lam i * (v i j : ℝ)) ∧
      (∀ i ∈ Finset.Icc 1 k, supNorm (v i) ≤ N ^ n) ∧
      CondIII N k lam v := by sorry

end DiophantinePreprocessing.FrankTardos
