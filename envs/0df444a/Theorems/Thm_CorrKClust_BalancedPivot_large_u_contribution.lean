-- Prove2me | Theorems.Thm_CorrKClust_BalancedPivot_large_u_contribution
-- name    : CorrKClust.BalancedPivot.large_u_contribution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:48.371591+00:00
-- url     : https://prove2.me/theorems/fd1ff803-e8cd-4d75-bcb9-a0091f70ee03
-- title:
--   §7.3.4, Case 1 — Large-U expected merging contribution
-- statement:
--   There is an absolute C > 0 such that for every graph on n ≥ 2 vertices, every k ≥ 1 and every admissible tie rule,
--   $$\mathbb E_\sigma[\operatorname{Cost}_{merge}(\sigma)\mathbf1_{\mathcal L}(\sigma)]\le C\ln n\operatorname{OPT}_k(G).$$
--   Here $T$ precedes pivot k+1, $U$ is uncovered at T, $S_1$ consists of early pivot clusters with at most $2048\ln n$ arrivals by T, and
--   $$\mathcal L=\left\{T<n,\ |U|>512|S_1|\frac{n\ln n}{2^{\lfloor\log_2 T\rfloor}}\right\}.$$
--   The constants defining the case are the paper's β = 2048 and c₂ = 512. The statement is the final multiplicative conclusion after the paper absorbs the additive term using integrality; it includes OPT = 0, where merging cost vanishes identically.
--
--   Differences from the source:
--   - encoding: finite vertex set and unordered disagreements → Fintype V, SimpleGraph V, maps to labels, and unordered distinct Sym2 pairs; reason: decidable equality is classical data and no finite graph or clustering is excluded
--   - encoding: every finite vertex set → vertex types V : Type (universe 0); reason: every finite vertex set is in bijection with Fin n : Type, and cost, OPT_k and the algorithm transfer along such bijections
--   - encoding: at most k possibly empty clusters → k > 0 and assignments V → Fin k; reason: positive k is required for an assignment on nonempty inputs and all unused labels remain legal
--   - encoding: uniform random arrival order → the finite average over all bijections Fin (card V) ≃ V; reason: there are exactly n! such bijections, each with equal weight
--   - encoding: n ≥ 2 for the remainder of §7.3.2–§7.3.4, p. 30 → 2 ≤ Fintype.card V; reason: this is the stated standing assumption, ensuring positive natural logarithms and denominators
--   - reading: assign to the cluster with minimal size, with ties unspecified → every history-dependent rule returning a minimum-current-size cluster; reason: the proof uses only minimality and the absolute constant must be uniform over these choices
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), §7.3.4, Case 1 conclusion, pp. 38–41, p. 41, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/302.pdf

import Definitions.Def_CorrKClust_BalancedPivot_Analysis

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot

/-- §7.3.4, Large-U conclusion: no additive error, including OPT = 0. -/
theorem large_u_contribution : ∃ C : ℝ, 0 < C ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    2 ≤ Fintype.card V → ∀ (k : ℕ) (hk : 0 < k) (ρ : TieRule V k), Admissible ρ →
    contribution (fun σ : ArrivalOrder V => (mergeCost hk G ρ σ : ℝ)) (LargeU G k) ≤
      C * Real.log (Fintype.card V) ^ 1 * (optK G k : ℝ) := by sorry

end CorrKClust.BalancedPivot
