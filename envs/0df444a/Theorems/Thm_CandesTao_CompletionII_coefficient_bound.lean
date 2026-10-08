-- Prove2me | Theorems.Thm_CandesTao_CompletionII_coefficient_bound
-- name    : CandesTao.CompletionII.coefficient_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:54:38.455907+00:00
-- url     : https://prove2.me/theorems/1b52fed6-ec23-425b-aa61-96f9e94e7db5
-- title:
--   Lemma 8.2 — Size of the expansion coefficients
-- statement:
--   Let $n, r, m$ be natural numbers with $0 < m \le n^2$ and $2nr \le m$ (the standing assumption (I.22)). Put $p := m/n^2$, $\rho' := 2r/n - (r/n)^2$ and $\lambda := \rho'/p$; assumption (I.22) gives $\lambda < 1$ when $r \ge 1$. Let $\alpha^{(k)}, \beta^{(k)}, \gamma^{(k)}, \delta^{(k)}$ be the coefficient sequences of Lemma 8.1 for these $p, \rho'$. Then for all $j, k \ge 0$,
--   $$\max\left(\left|\alpha_j^{(k)}\right|, \left|\beta_j^{(k)}\right|, \left|\gamma_j^{(k)}\right|, \left|\delta_j^{(k)}\right|\right) \le \lambda^{\lceil\frac{k-j}{2}\rceil}4^k.$$
--
--   The bound says the coefficients grow at most like $4^k$ and decay geometrically in $\lambda$ as $j$ moves away from $k$. Together with Lemma 8.1 it gives Lemma 3.3.
--
--   **Formalization Note** The exponent $\lceil (k-j)/2\rceil$ is an integer ceiling of a real number and may be negative (for $j > k+1$); the power is an integer power. For $j > k$ every coefficient is zero. When $r = 0$, $\lambda = 0$ and Lean's convention $0^{-n} = 0$ is harmless because the coefficients vanish in that range.
-- source:
--   Candès & Tao, The Power of Convex Relaxation: Near-Optimal Matrix Completion, IEEE Trans. Inf. Theory 56(5), 2010, p. 2079, Lemma 8.2, Eq. (VIII.3); assumption (I.22) on p. 2059

import Definitions.Def_CandesTao_CompletionII_CenteredOperators
import Definitions.Def_CandesTao_CompletionII_ExpansionCoefficients

open MatrixCompletion

namespace CandesTao.CompletionII

/-- Candès–Tao, Lemma 8.2 (bound (VIII.3)).  Let `n, r, m` satisfy the standing
assumption (I.22) `2nr ≤ m`, with `0 < m ≤ n²`, put `p := m/n²`, `ρ' := 2(r/n) - (r/n)²`
and `λ := ρ'/p` (so `λ < 1` when `r ≥ 1`).  Then the coefficient sequences of Lemma 8.1
obey, for all `j, k ≥ 0`,
`max(|α^{(k)}_j|, |β^{(k)}_j|, |γ^{(k)}_j|, |δ^{(k)}_j|) ≤ λ^{⌈(k-j)/2⌉} 4^k`,
with an integer (possibly negative) exponent. -/
theorem coefficient_bound (n r m : ℕ) (hm : 0 < m) (hmn : m ≤ n * n)
    (hI22 : 2 * n * r ≤ m) (k j : ℕ) :
    let p : ℝ := (m : ℝ) / (n : ℝ) ^ 2
    let lam : ℝ := rhoPrime n r / p
    let c := expansionCoeffs p (rhoPrime n r) k
    max (max |c.α j| |c.β j|) (max |c.γ j| |c.δ j|) ≤
      lam ^ ⌈((k : ℝ) - (j : ℝ)) / 2⌉ * 4 ^ k := by sorry

end CandesTao.CompletionII
