-- Prove2me | Theorems.Thm_CubeSampling_theorem_2_1
-- name    : CubeSampling.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:20:11.389074+00:00
-- url     : https://prove2.me/theorems/cc486ed1-5d29-404f-816b-23de7454661c
-- title:
--   Theorem 2.1 — El Hanchi–Maddison–Erdogdu quantile formula
-- statement:
--   **Theorem 2.1** (El Hanchi–Maddison–Erdogdu, [EHE24]). For a fixed known subspace $V$ in (1) with orthonormal basis $\Phi$, noise level $\sigma > 0$, sample size $n \ge 1$ and $\delta \in (0,1)$, let $G \sim N(0, I_m)$ be independent of the sampled inputs and
--   $$
--   Z_{n,V} = \begin{cases} (\sigma^2/n)\,G^\top\hat\Sigma_V^{-1}G, & \hat\Sigma_V \text{ invertible},\\ +\infty, & \hat\Sigma_V \text{ singular}.\end{cases}
--   $$
--   Then
--
--   1. $R^*_{n,\delta}(V) = Q_{1-\delta}(Z_{n,V})$;
--   2. any measurable least-squares minimizer $\hat\theta$ (an estimator whose value minimizes $\sum_i (Y_i - a^\top\Phi(X_i))^2$ over $a \in \mathbb R^m$ on every data set) attains this minimax value: $\sup_\theta Q_{1-\delta,\theta}(\|\hat\theta - \theta\|_2^2) = R^*_{n,\delta}(V)$;
--   3. $R^*_{n,\delta}(V) = +\infty$ if and only if $P(\hat\Sigma_V \text{ singular}) \ge \delta$.
--
--   This exact formula turns sampling bounds for $\hat\Sigma_V$ into minimax risk bounds in both directions.
--
--   Differences from the source:
--   - encoding: an m-dimensional subspace V with its orthonormal basis Φ_V → an orthonormal family Φ : Fin m → (cube → ℝ); reason: the paper notes the choice of basis is arbitrary; V = span Φ
--   - encoding: estimators with any randomness; probabilities include estimator randomness → measurable maps of the data and an independent U ~ Uniform[0,1]; reason: standard representation of randomized estimators; deterministic estimators are included
--   - encoding: Q_{1−δ}(Z) = inf{r ≥ 0 : P(Z ≤ r) ≥ 1 − δ}, inf ∅ = +∞ → infimum in [0,∞] over finite r; reason: same quantity: r is a real number in the paper
--   - generalization: V the model of (1), V ⊆ P_{d,k} → V the span of any orthonormal family of functions on the cube; reason: the cited result [EHE24] is for an arbitrary known model; it specializes to V ⊆ P_{d,k}
--   - reading: δ left implicit → δ ∈ (0,1); reason: a confidence level (t = log(1/δ) > 0)
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Theorem 2.1, p.7

import Mathlib
import Definitions.Def_CubeSampling_minimaxRisk
import Definitions.Def_CubeSampling_IsOrthonormalFamily
import Definitions.Def_CubeSampling_cubeMeasure
import Definitions.Def_CubeSampling_empCov
import Definitions.Def_CubeSampling_zStat
import Definitions.Def_CubeSampling_quantile
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CubeSampling

/-- Theorem 2.1 (El Hanchi–Maddison–Erdogdu, [EHE24]) (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), Theorem 2.1, p.7): for a fixed known
subspace `V` in (1), let `G ~ N(0, I_m)` be independent of the sampled inputs and `Z_{n,V}` as in `zStat`.
Then `R*_{n,δ}(V) = Q_{1−δ}(Z_{n,V})`, and any measurable least-squares minimizer attains this minimax
value. Moreover, `R*_{n,δ}(V) = +∞` if and only if `Pr(Σ̂_V singular) ≥ δ`.

**Formalization Note** `δ ∈ (0, 1)`, `σ > 0`; a least-squares minimizer is an estimator whose
output minimizes `∑_i (Y_i − a^⊤Φ(X_i))²` over `a ∈ ℝ^m` on every data set (whatever the value of `U`). -/
theorem theorem_2_1 {d m : ℕ} (Φ : Fin m → Cube d → ℝ) (hΦ : IsOrthonormalFamily Φ)
    (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1) :
    minimaxRisk Φ σ n δ =
        quantile ((Measure.pi fun _ : Fin n => cubeMeasure d).prod
          (Measure.pi fun _ : Fin m => gaussianReal 0 1)) (zStat Φ σ n) δ ∧
    (∀ est : (Fin n → Cube d × ℝ) × unitInterval → (Fin m → ℝ), Measurable est →
      (∀ (ω : Fin n → Cube d × ℝ) (u : unitInterval) (a : Fin m → ℝ),
        ∑ i, ((ω i).2 - ∑ j, est (ω, u) j * Φ j (ω i).1) ^ 2 ≤
          ∑ i, ((ω i).2 - ∑ j, a j * Φ j (ω i).1) ^ 2) →
      (⨆ θ : Fin m → ℝ, riskQuantile Φ σ n δ est θ) = minimaxRisk Φ σ n δ) ∧
    (minimaxRisk Φ σ n δ = ⊤ ↔
      ENNReal.ofReal δ ≤ (Measure.pi fun _ : Fin n => cubeMeasure d) {X | ¬ IsUnit (empCov Φ n X).det}) := by sorry

end CubeSampling
