-- Prove2me | Theorems.Thm_DiophantinePreprocessing_FrankTardos_preprocessing_output_criteria
-- name    : DiophantinePreprocessing.FrankTardos.preprocessing_output_criteria
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:41:54.430827+00:00
-- url     : https://prove2.me/theorems/d5356ef4-6bf1-4281-b8a1-249123e7c59a
-- title:
--   Theorem 3.3 — the preprocessed vector $\tilde w$ satisfies the output criteria
-- statement:
--   Let $N \ge 1$ be an integer and $w \in \mathbb{Q}^n$ a rational vector. Suppose that (Step 1 of the preprocessing algorithm)
--   $$w = \sum_{i=1}^k \lambda_i v_i$$
--   with $k \le n$, $\lambda_i > 0$ real, $v_i \in \mathbb{Z}^n$, the bound (ii)' $\|v_i\|_\infty \le 2^{n^2+n} N^n$ for $i = 1, \dots, k$, and condition (iii) with the integer $N$. Let (Step 2)
--   $$M = 2^{n^2+n} N^{n+1}, \qquad \tilde w = \sum_{i=1}^k M^{k-i} v_i \in \mathbb{Z}^n.$$
--   Then $\tilde w$ satisfies the output criteria:
--
--   1. $\|\tilde w\|_\infty \le 2^{4n^3} N^{n(n+2)}$, and
--   2. $\operatorname{sign}(w \cdot b) = \operatorname{sign}(\tilde w \cdot b)$ for every integer vector $b \in \mathbb{Z}^n$ with $\|b\|_1 \le N - 1$.
--
--   The theorem turns an arbitrary rational objective into an integral one whose size depends only on $n$ and $\log N$, without changing which side of any hyperplane $\{x : b \cdot x = 0\}$ with small integral $b$ it lies on.
--
--   **Formalization Note** The theorem is stated for every decomposition meeting the conditions of Step 1, not only for the one produced by the decomposing algorithm; the coefficients $\lambda_i$ are real. $\|b\|_1$ is the explicit sum $\sum_j |b(j)|$ compared in $\mathbb{Z}$, and sign equality includes the zero case.
-- source:
--   Frank & Tardos, An application of simultaneous diophantine approximation in combinatorial optimization, Combinatorica 7(1) (1987), p. 56, Theorem 3.3; Preprocessing algorithm p. 55 (Output, Steps 1–2); condition (ii)' p. 54

import Mathlib
import Definitions.Def_DiophantinePreprocessing_FrankTardos_CondIII

namespace DiophantinePreprocessing.FrankTardos

/-- Frank–Tardos, Theorem 3.3 (p. 56), for the preprocessing algorithm of p. 55: given a
decomposition `w = ∑_{i=1}^k λ_i v_i` of a rational vector `w` as in Step 1 (`k ≤ n`, `λ_i > 0`,
integer `v_i`, condition (ii)' `‖v_i‖∞ ≤ 2^{n²+n} Nⁿ`, condition (iii)), the Step 2 vector
`w̃ = ∑_{i=1}^k M^{k-i} v_i` with `M = 2^{n²+n} N^{n+1}` satisfies the output criteria:
`‖w̃‖∞ ≤ 2^{4n³} N^{n(n+2)}` and `sign (w · b) = sign (w̃ · b)` for every integer `b` with
`‖b‖₁ ≤ N - 1`. -/
theorem preprocessing_output_criteria (n N k : ℕ) (hN : 1 ≤ N) (w : Fin n → ℚ)
    (v : ℕ → Fin n → ℤ) (lam : ℕ → ℝ) (hk : k ≤ n)
    (hlam : ∀ i ∈ Finset.Icc 1 k, 0 < lam i)
    (hw : ∀ j, (w j : ℝ) = ∑ i ∈ Finset.Icc 1 k, lam i * (v i j : ℝ))
    (hii' : ∀ i ∈ Finset.Icc 1 k, supNorm (v i) ≤ 2 ^ (n ^ 2 + n) * N ^ n)
    (hIII : CondIII N k lam v) :
    let M : ℤ := 2 ^ (n ^ 2 + n) * (N : ℤ) ^ (n + 1)
    let wt : Fin n → ℤ := fun j => ∑ i ∈ Finset.Icc 1 k, M ^ (k - i) * v i j
    (∀ j, |wt j| ≤ 2 ^ (4 * n ^ 3) * (N : ℤ) ^ (n * (n + 2))) ∧
    ∀ b : Fin n → ℤ, ∑ j, |b j| ≤ (N : ℤ) - 1 →
      SignType.sign (∑ j, (w j : ℝ) * (b j : ℝ)) =
        SignType.sign ((∑ j, wt j * b j : ℤ) : ℝ) := by sorry

end DiophantinePreprocessing.FrankTardos
