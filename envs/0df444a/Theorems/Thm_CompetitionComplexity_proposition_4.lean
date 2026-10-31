-- Prove2me | Theorems.Thm_CompetitionComplexity_proposition_4
-- name    : CompetitionComplexity.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:29:10.664345+00:00
-- url     : https://prove2.me/theorems/ba740bcf-b175-42f3-8fa9-3316385b2254
-- title:
--   Proposition 4 — replacing the tail of a feasible $\delta$ with $\delta_m/\delta_{m-1}<1$ by a geometric one
-- statement:
--   Let $n,m$ be positive integers and let $(\delta_j)$ satisfy (2)–(4) ($\delta$ non-increasing, $\delta_j^2\le\delta_{j-1}\delta_{j+1}$, $\delta_0=1$, $\delta_j>0$) with $\delta_m/\delta_{m-1}<1$. Then there is a sequence $(\beta_j)$ satisfying (2)–(4) such that
--
--   1. **(a)** $\delta_j=\beta_j$ for every $j\in\{0,1,\dots,m-1\}$, and $\beta_m/\beta_{m-1}<1$;
--   2. **(b)**
--   $$
--   \sum_{i=m-1}^{\infty}\Bigl(1-\Bigl(\frac{\delta_{i+1}}{\delta_i}\Bigr)^n\Bigr)\delta_i\le\beta_{m-1}\sum_{i=0}^{n-1}\Bigl(\frac{\beta_m}{\beta_{m-1}}\Bigr)^i .
--   $$
--
--   This lets the proof of Lemma 4 reduce the tail of the objective (1) to a geometric tail, leaving a finite-dimensional problem.
--
--   **Formalization Note** The tail series is summable for every feasible $\delta$ (proved in the mission's verification file), so Lean's `tsum` is its sum.
--
--   Differences from the source:
--   - reading: n and m not restricted in the statement (§5 works with n ≥ 2, m ≥ 3) → all integers n ≥ 1 and m ≥ 1; reason: the proposition fixes no range; positive integers n, m are the setting of Theorem 3 and contain §5's range, and neither the statement nor the proof uses more
-- source:
--   Brustle, Correa, Dütting, Verdugo, The Competition Complexity of Dynamic Pricing, accepted manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), doi:10.1287/moor.2022.0230, Proposition 4, p.18

import Mathlib
import Definitions.Def_CompetitionComplexity_Program

namespace CompetitionComplexity

/-- **Proposition 4** (geometric tail replacement).
Brustle, Correa, Dütting, Verdugo, *The Competition Complexity of Dynamic Pricing*, accepted
manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), Proposition 4, p.18:
"For every sequence (δj)j∈N satisfying (2)-(4) for which δm/δm−1 < 1, there exists a sequence
(βj)j∈N satisfying (2)-(4), and such that the following holds:
(a) For every j ∈ {0,1,...,m−1} we have δj = βj, and βm/βm−1 < 1.
(b) Σ_{i=m−1}^∞ (1 − (δi+1/δi)^n) δi ≤ βm−1 Σ_{i=0}^{n−1} (βm/βm−1)^i."

**Formalization Note.** The proposition fixes no range for `n` and `m`; it is stated for all
positive integers `n`, `m` (the setting of Theorem 3), which contains the `n ≥ 2`, `m ≥ 3` of §5.
The tail series is the `tsum` of `tailTerm n δ (i + (m − 1))`; it is summable for every feasible
`δ` (proved in the verification file), so `tsum` is its sum. -/
theorem proposition_4 (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (δ : ℕ → ℝ) (hδ : Feasible δ)
    (hlt : δ m / δ (m - 1) < 1) :
    ∃ β : ℕ → ℝ, Feasible β ∧ (∀ j : ℕ, j < m → δ j = β j) ∧ β m / β (m - 1) < 1 ∧
      ∑' i : ℕ, tailTerm n δ (i + (m - 1)) ≤
        β (m - 1) * ∑ i ∈ Finset.range n, (β m / β (m - 1)) ^ i := by sorry

end CompetitionComplexity
