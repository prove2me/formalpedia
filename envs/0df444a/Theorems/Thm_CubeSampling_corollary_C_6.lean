-- Prove2me | Theorems.Thm_CubeSampling_corollary_C_6
-- name    : CubeSampling.corollary_C_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:21:25.700221+00:00
-- url     : https://prove2.me/theorems/c8bf4d31-446c-4ef2-9ec9-5a7171536938
-- title:
--   Corollary C.6 — OLS after lower conditioning
-- statement:
--   **Corollary C.6.** Let $V$ have orthonormal basis $\Phi_V$, $\sigma > 0$, $n \ge 1$ and $0 < \delta \le 1/4$. If $X_1, \dots, X_n$ i.i.d. $\mu_d$ satisfy
--   $$
--   P\bigl(\hat\Sigma_V \succeq \tfrac12 I_m\bigr) \ge 1 - \delta/2,
--   $$
--   then
--   $$
--   R^*_{n,\delta}(V) \le 12\,\sigma^2\,\frac{m + \log(1/\delta)}{n},
--   $$
--   and every measurable ordinary least-squares rule satisfies the same bound uniformly over $\theta$: $Q_{1-\delta,\theta}(\|\hat\theta_{\mathrm{OLS}} - \theta\|_2^2) \le 12\sigma^2(m + \log(1/\delta))/n$ for all $\theta \in \mathbb R^m$.
--
--   With Propositions 3.3 and 3.4 this yields the upper bound of Theorem 1.5 with constant $12 \le A$.
--
--   Differences from the source:
--   - encoding: an m-dimensional subspace V with its orthonormal basis Φ_V → an orthonormal family Φ : Fin m → (cube → ℝ); reason: the paper notes the choice of basis is arbitrary; V = span Φ
--   - encoding: estimators with any randomness; probabilities include estimator randomness → measurable maps of the data and an independent U ~ Uniform[0,1]; reason: standard representation of randomized estimators; deterministic estimators are included
--   - encoding: Q_{1−δ}(Z) = inf{r ≥ 0 : P(Z ≤ r) ≥ 1 − δ}, inf ∅ = +∞ → infimum in [0,∞] over finite r; reason: same quantity: r is a real number in the paper
--   - generalization: V the model of (1), V ⊆ P_{d,k} → V the span of any orthonormal family of functions on the cube; reason: the corollary and its proof use only orthonormality; it specializes to V ⊆ P_{d,k}
--   - generalization: OLS (a least-squares minimizer) → every measurable rule equal to the least-squares solution on nonsingular designs, arbitrary on singular ones; reason: contains every measurable least-squares minimizer, so it specializes to the paper's OLS
--   - reading: δ ≤ 1/4 (with t = log(1/δ)) → 0 < δ ≤ 1/4; reason: log(1/δ) must be finite
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Corollary C.6, p.34

import Mathlib
import Definitions.Def_CubeSampling_minimaxRisk
import Definitions.Def_CubeSampling_IsOrthonormalFamily
import Definitions.Def_CubeSampling_cubeMeasure
import Definitions.Def_CubeSampling_empCov
import Definitions.Def_CubeSampling_IsOLSRule
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CubeSampling

/-- Corollary C.6 (OLS after lower conditioning) (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), Corollary C.6, p.34): if
`P(Σ̂_V ⪰ ½ I_m) ≥ 1 − δ/2`, where `δ ≤ 1/4`, then `R*_{n,δ}(V) ≤ 12σ² (m + log(1/δ)) / n`; OLS satisfies the
same bound uniformly over `θ`.

**Formalization Note** `0 < δ`, `σ > 0`; `V` is any space of functions on the cube with an
orthonormal basis `Φ`; "OLS" is every measurable OLS rule (`IsOLSRule`). -/
theorem corollary_C_6 {d m : ℕ} (Φ : Fin m → Cube d → ℝ) (hΦ : IsOrthonormalFamily Φ)
    (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4)
    (hcond : ENNReal.ofReal (1 - δ / 2) ≤ (Measure.pi fun _ : Fin n => cubeMeasure d)
        {X | (empCov Φ n X - (1 / 2 : ℝ) • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef}) :
    minimaxRisk Φ σ n δ ≤ ENNReal.ofReal (12 * σ ^ 2 * (m + Real.log (1 / δ)) / n) ∧
    ∀ est : (Fin n → Cube d × ℝ) × unitInterval → (Fin m → ℝ), Measurable est →
      IsOLSRule Φ n est → ∀ θ : Fin m → ℝ,
        riskQuantile Φ σ n δ est θ ≤ ENNReal.ofReal (12 * σ ^ 2 * (m + Real.log (1 / δ)) / n) := by sorry

end CubeSampling
