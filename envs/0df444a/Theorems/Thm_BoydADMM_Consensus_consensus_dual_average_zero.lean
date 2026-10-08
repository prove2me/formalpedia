-- Prove2me | Theorems.Thm_BoydADMM_Consensus_consensus_dual_average_zero
-- name    : BoydADMM.Consensus.consensus_dual_average_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:06:23.426983+00:00
-- url     : https://prove2.me/theorems/d3029f80-126b-4670-bfc2-b1595f6dd335
-- title:
--   Consensus ADMM: $\bar y^{k+1}=0$, $z^k=\bar x^k$ and the simplified iteration
-- statement:
--   Let $x_i^k, z^k, y_i^k$ be any run of global variable consensus ADMM (§7.1) with $N\ge1$ agents and $\rho>0$. Then:
--
--   1. the dual variables have average zero after the first iteration: $\bar y^{k+1}=0$ for every $k\ge0$;
--   2. $z^k=\bar x^k$ for every $k\ge2$;
--   3. for every $k\ge2$, $x_i^{k+1}$ minimizes $f_i(x_i)+y_i^{kT}(x_i-\bar x^k)+(\rho/2)\|x_i-\bar x^k\|_2^2$ over $\operatorname{dom} f_i$;
--   4. for every $k\ge1$, $y_i^{k+1}=y_i^k+\rho(x_i^{k+1}-\bar x^{k+1})$.
--
--   Items 3–4 are the book's simplified algorithm, in which the global variable $z$ no longer appears:
--   $$x_i^{k+1}:=\operatorname*{argmin}_{x_i}\big(f_i(x_i)+y_i^{kT}(x_i-\bar x^k)+(\rho/2)\|x_i-\bar x^k\|_2^2\big),\qquad y_i^{k+1}:=y_i^k+\rho(x_i^{k+1}-\bar x^{k+1}).$$
--
--   **Formalization Note** The book says "after the first iteration" and then "using $z^k=\bar x^k$" without an index range. Since $z^{k}=\bar x^{k}+(1/\rho)\bar y^{k-1}$, the identity $z^k=\bar x^k$ needs $\bar y^{k-1}=0$, i.e. $k\ge2$ for an arbitrary starting $y^0$; we state exactly these ranges. $N\ge1$ and $\rho>0$ are made explicit.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 50, §7.1 (ȳ^{k+1} = 0 and the simplified algorithm)

import Mathlib
import Definitions.Def_BoydADMM_Consensus_Model

open scoped BigOperators InnerProductSpace

namespace BoydADMM.Consensus

/-- §7.1, p. 50: along every run of global variable consensus ADMM with `N ≥ 1`, `ρ > 0`:
(1) `ȳ^{k+1} = 0` for every `k ≥ 0` (the dual variables have average zero after the first
iteration); (2) `z^k = x̄^k` for every `k ≥ 2`; and hence the simplified iteration holds:
(3) for `k ≥ 2`, `x_i^{k+1}` minimizes `f_i(x_i) + y_i^{kT}(x_i − x̄^k) + (ρ/2)‖x_i − x̄^k‖²` over
`dom f_i`, and (4) for `k ≥ 1`, `y_i^{k+1} = y_i^k + ρ(x_i^{k+1} − x̄^{k+1})`. -/
theorem consensus_dual_average_zero {n N : ℕ} (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (Cf : Fin N → Set (EuclideanSpace ℝ (Fin n))) (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : ℕ → Fin N → EuclideanSpace ℝ (Fin n)) (z : ℕ → EuclideanSpace ℝ (Fin n))
    (y : ℕ → Fin N → EuclideanSpace ℝ (Fin n)) (hrun : IsConsensusADMMRun Cf f ρ x z y) :
    (∀ k, avg (y (k + 1)) = 0) ∧
    (∀ k, 2 ≤ k → z k = avg (x k)) ∧
    (∀ k, 2 ≤ k → ∀ i, ∀ x' ∈ Cf i,
      f i (x (k + 1) i) + ⟪y k i, x (k + 1) i - avg (x k)⟫_ℝ +
          (ρ / 2) * ‖x (k + 1) i - avg (x k)‖ ^ 2 ≤
        f i x' + ⟪y k i, x' - avg (x k)⟫_ℝ + (ρ / 2) * ‖x' - avg (x k)‖ ^ 2) ∧
    (∀ k, 1 ≤ k → ∀ i, y (k + 1) i = y k i + ρ • (x (k + 1) i - avg (x (k + 1)))) := by sorry

end BoydADMM.Consensus
