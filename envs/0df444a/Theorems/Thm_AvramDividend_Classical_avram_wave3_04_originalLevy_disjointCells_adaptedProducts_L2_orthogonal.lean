-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_originalLevy_disjointCells_adaptedProducts_L2_orthogonal
-- name    : AvramDividend.Classical.avram_wave3_04_originalLevy_disjointCells_adaptedProducts_L2_orthogonal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:18:53.688016+00:00
-- url     : https://prove2.me/theorems/14c775f0-30bc-4afc-91df-b35eba9b4682
-- title:
--   Non-overlapping original Lévy future-increment cells with bounded adapted coefficients have zero covariance
-- statement:
--   Take an arbitrary original spectrally negative Lévy process with its actual full filtration, and two non-overlapping deterministic time cells s≤t≤u≤v. The earlier cell payoff φ(X_t−X_s) is bounded by R and Borel measurable, its coefficient H is bounded and measurable in the true history F_s, and the later cell coefficient K is bounded and measurable in F_u. The later future payoff ψ(X_v−X_u) is integrable under the actual stationary increment law and has centred expectation. The product of the earlier cell payoff and both adapted coefficients is strongly F_u measurable, since all earlier process values are F_u adapted, and is bounded by A·R·B. The already canonical Proved original-process bounded-past centred-increment expectation theorem applies at u,v with exactly that combined earlier coefficient and proves the two stochastic cell terms have zero covariance. This is a nontrivial original-filtration L² orthogonality interface toward controlled stochastic integral isometries; no independent copy or surrogate Brownian process is used.
-- source:
--   Pinned remote private compiler probe job 0fd04968-8e61-4776-8822-fb9601232551 reached its intentional sentinel with zero candidate diagnostics, source SHA256 f9203bbc46b2365a56e14b43a10b0b051b228682f110980dc477c25e6ae4ed44. Canonical Proved boundedPast_centeredFuture_increment_mean_zero UUID 488296c2-5a96-4786-a577-a02199ace877. Source X.adapted and filtration monotonicity, Mathlib measurable multiplication and norm multiplication.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_boundedPast_centeredFuture_increment_mean_zero

open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_originalLevy_disjointCells_adaptedProducts_L2_orthogonal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t u v : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v)
    (H K : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕 s] H)
    (hK : StronglyMeasurable[𝓕 u] K)
    (A B R : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hR0 : 0 ≤ R)
    (hHb : ∀ ω, ‖H ω‖ ≤ A) (hKb : ∀ ω, ‖K ω‖ ≤ B)
    (φ ψ : ℝ → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ)
    (hφb : ∀ z, ‖φ z‖ ≤ R)
    (hψInt : Integrable (fun ω => ψ (X.X (v - u) ω)) P)
    (hψMean : (∫ ω, ψ (X.X (v - u) ω) ∂P) = 0) :
    (∫ ω, (H ω * φ (X.X t ω - X.X s ω)) *
      (K ω * ψ (X.X v ω - X.X u ω)) ∂P) = 0 := by sorry
