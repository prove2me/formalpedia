-- Prove2me | Theorems.Thm_CorrKClust_BalancedPivot_small_u_contribution
-- name    : CorrKClust.BalancedPivot.small_u_contribution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:52.694002+00:00
-- url     : https://prove2.me/theorems/fa39a9ea-58bb-42ff-8d15-9d1cf1a3581a
-- title:
--   §7.3.4, Case 2 — Small-U expected merging contribution
-- statement:
--   There is an absolute C > 0 such that for every graph on n ≥ 2 vertices, every k ≥ 1 and every admissible tie rule,
--   $$\mathbb E_\sigma[\operatorname{Cost}_{merge}(\sigma)\mathbf1_{\mathcal B}(\sigma)]\le C(\ln n)^4\operatorname{OPT}_k(G).$$
--   Using T, U and S₁ as in the Large-U milestone, with β = 2048 and c₂ = 512, the event is
--   $$\mathcal B=\left\{T<n,\ |U|\le512|S_1|\frac{n\ln n}{2^{\lfloor\log_2 T\rfloor}}\right\}.$$
--   The statement covers every graph and both regimes for the number of optimal unconstrained blocks. No additive error remains, including when OPT = 0. This is the complementary merging contribution needed for the goal.
--
--   Differences from the source:
--   - encoding: finite vertex set and unordered disagreements → Fintype V, SimpleGraph V, maps to labels, and unordered distinct Sym2 pairs; reason: decidable equality is classical data and no finite graph or clustering is excluded
--   - encoding: every finite vertex set → vertex types V : Type (universe 0); reason: every finite vertex set is in bijection with Fin n : Type, and cost, OPT_k and the algorithm transfer along such bijections
--   - encoding: at most k possibly empty clusters → k > 0 and assignments V → Fin k; reason: positive k is required for an assignment on nonempty inputs and all unused labels remain legal
--   - encoding: uniform random arrival order → the finite average over all bijections Fin (card V) ≃ V; reason: there are exactly n! such bijections, each with equal weight
--   - encoding: n ≥ 2 for the remainder of §7.3.2–§7.3.4, p. 30 → 2 ≤ Fintype.card V; reason: this is the stated standing assumption, ensuring positive natural logarithms and denominators
--   - reading: assign to the cluster with minimal size, with ties unspecified → every history-dependent rule returning a minimum-current-size cluster; reason: the proof uses only minimality and the absolute constant must be uniform over these choices
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), §7.3.4, Case 2 conclusion, pp. 41–46, p. 46, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/302.pdf

import Definitions.Def_CorrKClust_BalancedPivot_Analysis

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot

/-- §7.3.4, Small-U conclusion: no additive error, including OPT = 0. -/
theorem small_u_contribution : ∃ C : ℝ, 0 < C ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    2 ≤ Fintype.card V → ∀ (k : ℕ) (hk : 0 < k) (ρ : TieRule V k), Admissible ρ →
    contribution (fun σ : ArrivalOrder V => (mergeCost hk G ρ σ : ℝ)) (SmallU G k) ≤
      C * Real.log (Fintype.card V) ^ 4 * (optK G k : ℝ) := by sorry

end CorrKClust.BalancedPivot
