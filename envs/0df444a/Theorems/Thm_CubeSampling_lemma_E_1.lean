-- Prove2me | Theorems.Thm_CubeSampling_lemma_E_1
-- name    : CubeSampling.lemma_E_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:22:41.511548+00:00
-- url     : https://prove2.me/theorems/1b1ec9cc-2744-4655-afdd-f7d9160cb5e1
-- title:
--   Lemma E.1 — baseline sample complexity $N_{\mathrm{par}} \ge c_0(m + \log(1/\delta))$
-- statement:
--   **Lemma E.1.** There is a universal $c_0 > 0$ such that for $d, k \ge 1$, $1 \le m \le D_{d,k}$, $0 < \delta \le 1/4$, $A \ge 16$ and every noise level $\sigma > 0$,
--   $$
--   N_{\mathrm{par}}(d,k,m,A,\delta) \ge c_0\,\bigl(m + \log(1/\delta)\bigr).
--   $$
--
--   It gives the lower bound of Theorem 1.5 for bounded $k$.
--
--   Differences from the source:
--   - reading: there is a universal c₀ > 0 → ∃ c₀ > 0 chosen before d, k, m, δ, A and σ; reason: 'universal' means independent of all parameters
--   - encoding: N_par an integer → N_par in ℕ∞; the bound stated for every finite value N; reason: when N_par = ∞ the bound holds trivially
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Lemma E.1, p.35

import Mathlib
import Definitions.Def_CubeSampling_Npar
import Definitions.Def_CubeSampling_dimLowDeg

namespace CubeSampling

/-- Lemma E.1 (baseline sample complexity) (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), Lemma E.1, p.35): for `d, k ≥ 1`, `1 ≤ m ≤ D_{d,k}`,
`0 < δ ≤ 1/4` and `A ≥ 16`, there is a universal `c₀ > 0` such that `N_par(d, k, m, A, δ) ≥ c₀ (m + log(1/δ))`.

**Formalization Note** `c₀` is chosen before every parameter (including `σ > 0`); when `N_par = ⊤` the
bound holds trivially, so it is stated for finite values `N`. -/
theorem lemma_E_1 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ d k : ℕ, 1 ≤ d → 1 ≤ k → ∀ m : ℕ, 1 ≤ m → m ≤ dimLowDeg d k →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 → ∀ A : ℝ, 16 ≤ A → ∀ σ : ℝ, 0 < σ →
      ∀ N : ℕ, Npar d k m A σ δ = N → c₀ * (m + Real.log (1 / δ)) ≤ N := by sorry

end CubeSampling
