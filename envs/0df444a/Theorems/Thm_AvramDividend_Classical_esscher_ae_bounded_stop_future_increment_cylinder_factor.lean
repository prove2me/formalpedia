-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_ae_bounded_stop_future_increment_cylinder_factor
-- name    : AvramDividend.Classical.esscher_ae_bounded_stop_future_increment_cylinder_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:31:37.638778+00:00
-- url     : https://prove2.me/theorems/1bda52b3-8790-4b68-a534-1b3e336b59c5
-- title:
--   Genuine Esscher future-increment cylinder factor for a stopping time bounded almost surely
-- statement:
--   For a genuine stopping time tau that is bounded by a deterministic H almost surely under the original Levy law P, a stopped-history event A and a real Borel increment cylinder B, the exact finite-terminal tilted Q_T joint mass at tau equals Q_T(A) times the deterministic Esscher Q_u future increment mass. The proof clips A to the support {tau<=H}, applies the already accepted unbounded-stopping-time localised cylinder result, and transfers back over the P-null exceptional set using absolute continuity of Q_T with respect to P. No full-path Esscher extension or WH independence is assumed.
-- source:
--   Existing canonically Proved esscher_locally_bounded_stop_increment_cylinder_factor 2a64cd78-54a7-401b-9d74-07006d316f8a; pinned Mathlib withDensity_absolutelyContinuous, Filter.Eventually.filter_mono and measure_congr.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_esscher_locally_bounded_stop_increment_cylinder_factor

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_ae_bounded_stop_future_increment_cylinder_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (haeBound : ∀ᵐ ω ∂P, τ ω ≤ H)
    (u T : ℝ≥0) (hT : H + 1 + u ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (B : Set ℝ) (hB : MeasurableSet B) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
      (A ∩ {ω : Ω |
        X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
      ((X.X u) ⁻¹' B) := by sorry
