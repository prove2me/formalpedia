-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04_originalLevy_two_cell_bounded_martingale_L2_isometry
-- name    : AvramDividend.Classical.avram_wave4_04_originalLevy_two_cell_bounded_martingale_L2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T20:31:04.490019+00:00
-- url     : https://prove2.me/theorems/e2cf17b0-fc18-426e-ae22-4fb581eb2f68
-- title:
--   Two-cell exact L2 isometry for bounded predictable original Lévy increment payoffs
-- statement:
--   For the actual spectrally negative Lévy process X on its original filtration, take deterministic disjoint cells s≤t≤u≤v. Allow arbitrary bounded coefficients H measurable in the true past F_s and K measurable in F_u, with bounded measurable increment payoffs φ and ψ, the later centred under the stationary increment law. The expectation of the square of the two-cell sum equals the sum of the individual second moments. This follows by genuine original-process L2 orthogonality, integrability of all squared and cross terms through source adaptedness and uniform bounds, and polynomial polarization, with no independent copied Brownian or Poisson process. It supplies an exact finite-grid second-moment building block for eventual controlled stochastic localisation, but does not establish the infinite-activity jump isometry or Ito-Meyer verification.
-- source:
--   Canonical Proved original disjoint-cell adapted products L2 orthogonality 14c775f0-30bc-4afc-91df-b35eba9b4682. Source X.adapted, stationary independent increments relative F, no same-law substitution. Unsubmitted Wave3 Chat04 complete source work/avram_wave3_04_original_two_cell_l2_isometry_probe.lean SHA256 28109712ad18009b030e4019629b47f8a4d32fcbcd79998e34ddc71ab7691701 preserved unchanged and copied into owned Wave4 path. Corrected UBV primary 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_originalLevy_disjointCells_adaptedProducts_L2_orthogonal

open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04_originalLevy_two_cell_bounded_martingale_L2_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t u v : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v)
    (H K : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕 s] H)
    (hK : StronglyMeasurable[𝓕 u] K)
    (A B R S : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hR0 : 0 ≤ R) (hS0 : 0 ≤ S)
    (hHb : ∀ ω, ‖H ω‖ ≤ A) (hKb : ∀ ω, ‖K ω‖ ≤ B)
    (φ ψ : ℝ → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ)
    (hφb : ∀ z, ‖φ z‖ ≤ R)
    (hψb : ∀ z, ‖ψ z‖ ≤ S)
    (hψMean : (∫ ω, ψ (X.X (v - u) ω) ∂P) = 0) :
    (∫ ω, (H ω * φ (X.X t ω - X.X s ω) +
      K ω * ψ (X.X v ω - X.X u ω)) ^ 2 ∂P) =
    (∫ ω, (H ω * φ (X.X t ω - X.X s ω)) ^ 2 ∂P) +
    (∫ ω, (K ω * ψ (X.X v ω - X.X u ω)) ^ 2 ∂P) := by sorry
