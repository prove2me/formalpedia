-- Prove2me | Theorems.Thm_DiophantinePreprocessing_FrankTardos_sign_first_nonzero
-- name    : DiophantinePreprocessing.FrankTardos.sign_first_nonzero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:41:25.594476+00:00
-- url     : https://prove2.me/theorems/b9766566-ee71-4cc6-a9bd-ed538092ab48
-- title:
--   Lemma 3.2 — the first non-orthogonal $v_j$ decides the sign of $b \cdot w$
-- statement:
--   Let $N \ge 1$ be an integer and let $w = \sum_{i=1}^k \lambda_i v_i \in \mathbb{R}^n$ where $\lambda_i > 0$, the $v_i \in \mathbb{Z}^n$ are integral, and the decomposition satisfies condition (iii) with $N$. Let $b \in \mathbb{Z}^n$ be an integer vector with
--   $$\|b\|_1 = \sum_{l=1}^n |b(l)| \le N - 1.$$
--   Then:
--
--   1. if $j \in \{1, \dots, k\}$ is the smallest index with $b \cdot v_j \ne 0$ (that is, $b \cdot v_i = 0$ for $1 \le i < j$ and $b \cdot v_j \ne 0$), then
--   $$\operatorname{sign}(b \cdot w) = \operatorname{sign}(b \cdot v_j);$$
--   2. if $b \cdot v_i = 0$ for every $i = 1, \dots, k$, then $b \cdot w = 0$.
--
--   Because the coefficients decrease fast, the vectors $v_i$ do not interact when $w$ is tested against a small integer vector $b$: the sign is decided by the first term that $b$ sees. This is what lets the preprocessing algorithm replace the real coefficients $\lambda_i$ by integer powers of a single number.
--
--   **Formalization Note** The sign function takes values $-1, 0, 1$ (`SignType.sign`), so equality of signs includes the case of zero. $N \ge 1$ is stated explicitly (for $N = 0$ no $b$ satisfies the hypothesis). No bound on $\|v_i\|_\infty$ and no $k \le n$ is assumed, as on the page.
-- source:
--   Frank & Tardos, An application of simultaneous diophantine approximation in combinatorial optimization, Combinatorica 7(1) (1987), pp. 54–55, Lemma 3.2

import Mathlib
import Definitions.Def_DiophantinePreprocessing_FrankTardos_CondIII

namespace DiophantinePreprocessing.FrankTardos

/-- Frank–Tardos, Lemma 3.2 (pp. 54–55): for a decomposition `w = ∑_{i=1}^k λ_i v_i` with
`λ_i > 0`, integer `v_i` and condition (iii), and an integer `b` with `‖b‖₁ ≤ N - 1`,
`sign (b · w) = sign (b · v_j)` for the smallest `j` with `b · v_j ≠ 0`, and `b · w = 0`
if `b · v_i = 0` for every `i`. -/
theorem sign_first_nonzero (n N k : ℕ) (hN : 1 ≤ N) (w : Fin n → ℝ)
    (v : ℕ → Fin n → ℤ) (lam : ℕ → ℝ)
    (hlam : ∀ i ∈ Finset.Icc 1 k, 0 < lam i)
    (hw : ∀ l, w l = ∑ i ∈ Finset.Icc 1 k, lam i * (v i l : ℝ))
    (hIII : CondIII N k lam v)
    (b : Fin n → ℤ) (hb : ∑ l, |b l| ≤ (N : ℤ) - 1) :
    (∀ j ∈ Finset.Icc 1 k,
        (∀ i ∈ Finset.Ico 1 j, ∑ l, b l * v i l = 0) → ∑ l, b l * v j l ≠ 0 →
        SignType.sign (∑ l, (b l : ℝ) * w l) = SignType.sign ((∑ l, b l * v j l : ℤ) : ℝ)) ∧
    ((∀ i ∈ Finset.Icc 1 k, ∑ l, b l * v i l = 0) → ∑ l, (b l : ℝ) * w l = 0) := by sorry

end DiophantinePreprocessing.FrankTardos
