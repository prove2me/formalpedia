-- Prove2me | Theorems.Thm_CascadeCC_lemma_4_domination
-- name    : CascadeCC.lemma_4_domination
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:34:37.419517+00:00
-- url     : https://prove2.me/theorems/a4d9a8da-0746-4b65-82c0-a98ab1a72554
-- title:
--   Proof of Lemma 4 — every feasible schedule is dominated by a stationary one
-- statement:
--   Let $\alpha=(\alpha_t)_{t\le N}$ be a feasible schedule of DET for $N\ge1$ periods and inventory $Y$. Then there are rates $a\in[0,u]^J$ with $N\sigma_j(a)a_j\le Y_j$ for all $j$ and
--
--   $$
--   \sum_{t}\sum_{j}\sigma_j(\alpha_t)r_j(\alpha_{tj})\ \le\ N\sum_j\sigma_j(a)r_j(a_j).
--   $$
--
--   This is the content of the permutation argument for Lemma 4, in a form that needs no optimal solution.
--
--   Differences from the source:
--   - encoding: prices in Ω_p as actions, rates in Ω_α = [0, u] or (0, u] → rates in [0, u] as actions, with 0 the turn-off price and revenue 0; reason: A1 makes prices and rates equivalent and §4.2 does the same; S(y) and S^D(y) contain rate 0, and [0, u] covers both forms of Ω_α
--   - generalization: A1 (α_j twice differentiable) and A2 → not assumed; the instance carries only p_j, strictly decreasing with p_j(u) = 0, and A3 with strict concavity, the derivatives and the bound |r″_j| ≤ w required on (0, u] only; reason: A1 and A2 concern the price parametrization, and for Ω_α = [0, u] the conditions of A3 on (0, u] are implied by those on [0, u]; every instance of A1–A3 is an instance here
--   - reading: σ_j = σ_{j−1}(1 − α_j)ζ_j on pp.10, 14, but σ_{j+1} = σ_j(1 − α_j)ζ_j on pp.20, 24, Figure 1 and (EC.19) → σ_j(a) = λ∏_{i<j}(1 − a_i)ζ_i; reason: the source disagrees with itself; the form of pp.20, 24 is the one its analysis uses and the printed one has an index slip
--   - generalization: for constant arrival rates there is an optimal constant solution, the proof written for T = 2 → every feasible schedule, for every N ≥ 1, is dominated by a feasible stationary one; reason: applied to an optimal schedule it gives the printed claim, and it does not need attainment
-- source:
--   Najafi, Duenyas, Jasin, Uichanco, Multi-product Dynamic Pricing with Limited Inventories under a Cascade Click Model, SSRN abstract_id=3362921, proof of Lemma 4, pp.ec7–8

import Mathlib
import Definitions.Def_CascadeCC_Analysis

namespace CascadeCC

variable {J : ℕ}

/-- The core of the proof of Lemma 4, pp.ec7–8 (SSRN abstract_id=3362921): every feasible schedule of DET
is dominated by a feasible stationary one.

**Formalization Note** The page shows that an optimal schedule may be taken constant. This domination form
is what survives without attainment, for every horizon; the printed proof treats T = 2. -/
theorem lemma_4_domination (M : Instance J) (N : ℕ) (hN : 0 < N) (Y : Fin J → ℝ)
    (α : Fin N → Fin J → ℝ) (hα : Feasible M N Y α) :
    ∃ a : Fin J → ℝ, (∀ j, a j ∈ Set.Icc 0 M.u) ∧ (∀ j, (N : ℝ) * purchase M a j ≤ Y j) ∧
      detObjective M N α ≤ (N : ℝ) * statObjective M a := by sorry

end CascadeCC
