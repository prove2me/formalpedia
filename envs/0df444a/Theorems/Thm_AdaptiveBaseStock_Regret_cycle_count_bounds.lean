-- Prove2me | Theorems.Thm_AdaptiveBaseStock_Regret_cycle_count_bounds
-- name    : AdaptiveBaseStock.Regret.cycle_count_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:16.411976+00:00
-- url     : https://prove2.me/theorems/f25a7c26-5b59-4101-82b7-543d4d162ec9
-- title:
--   Lemma 13 — relations between k, ⌈k^β⌉ and N(k) = Σ_{k′≤k} ⌈k′^β⌉
-- statement:
--   Let $\beta \in (0,1)$ and, for $k \ge 1$, let $N(k) = \sum_{k'=1}^k \lceil k'^\beta\rceil$. Then for every $k \ge 1$:
--
--   1. $k \le [(\beta+1)\, N(k)]^{1/(\beta+1)}$;
--   2. $k \cdot \lceil k^\beta\rceil \le 2(\beta+1)\, N(k)$;
--   3. $\lceil k^\beta\rceil \le 2\,[(\beta+1)\, N(k)]^{\beta/(\beta+1)}$;
--   4. $\lceil k^\beta\rceil^\alpha \le 2\,[(\beta+1)\, N(k)]^{\alpha\beta/(\beta+1)}$ for every $\alpha \in (0,1)$.
--
--   These inequalities convert bounds stated in the number of cycles into bounds in the number of periods $N(L)$.
-- source:
--   Huh, Janakiraman, Muckstadt, Rusmevichientong, An Adaptive Algorithm for Finding the Optimal Base-Stock Policy in Lost Sales Inventory Systems with Censored Demand, working paper, February 8, 2007 (published version: Math. Oper. Res., 2009, DOI 10.1287/moor.1080.0367), Lemma 13, p. 25 (proof in Appendix A, pp. 32–33)

import Mathlib
import Definitions.Def_AdaptiveBaseStock_Regret_Algorithm

namespace AdaptiveBaseStock.Regret

/-- Lemma 13, p. 25: with `N(k) = Σ_{k'=1}^k ⌈k'^β⌉` and `β ∈ (0, 1)`, for every `k ≥ 1`:
(i) `k ≤ [(β+1) N(k)]^{1/(β+1)}`; (ii) `k ⌈k^β⌉ ≤ 2(β+1) N(k)`;
(iii) `⌈k^β⌉ ≤ 2 [(β+1) N(k)]^{β/(β+1)}`; (iv) `⌈k^β⌉^α ≤ 2 [(β+1) N(k)]^{αβ/(β+1)}` for
every `α ∈ (0, 1)`. -/
theorem cycle_count_bounds (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) ≤ ((β + 1) * (periodsUpTo β k : ℝ)) ^ (1 / (β + 1)) ∧
    (k : ℝ) * (cycleLen β k : ℝ) ≤ 2 * (β + 1) * (periodsUpTo β k : ℝ) ∧
    (cycleLen β k : ℝ) ≤ 2 * ((β + 1) * (periodsUpTo β k : ℝ)) ^ (β / (β + 1)) ∧
    ∀ α : ℝ, 0 < α → α < 1 →
      (cycleLen β k : ℝ) ^ α ≤ 2 * ((β + 1) * (periodsUpTo β k : ℝ)) ^ (α * β / (β + 1)) := by sorry

end AdaptiveBaseStock.Regret
