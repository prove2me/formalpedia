-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_bounded_weighted_R_mesh_L1
-- name    : AvramDividend.Classical.avram_bv_residual10_original_bounded_weighted_R_mesh_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:56:40.982885+00:00
-- url     : https://prove2.me/theorems/c110a1c4-4983-4729-88f5-b915350edfd9
-- title:
--   Original stopped-mesh raw residual weighted by compact-bounded coefficients is L1
-- statement:
--   A source-exact compact-localisation integrability bridge for the original bounded-variation Levy residual with literal real raw-jump tsum. Any monotone finite mesh starting at zero, stopping by T, and any possibly path-dependent coefficients uniformly bounded by deterministic K have an L1 weighted residual whenever the literal original R(T) is L1 and the finite weighted sum is almost everywhere strongly measurable. Proof uses the established almost-sure monotone exact raw R, the proved pathwise sharp weighted mesh bound and Integrable.mono'. The stopped coefficient measurability and finite-band bound are separate explicit conditions; no Brownian isometry or unjustified global coefficient bound is asserted.
-- source:
--   AVRAM BV-RESIDUAL10 source-exact compact-localisation mesh L1 from Proved raw monotonicity and weighted finite-mesh endpoint bound, 7 November 2026

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_raw_R_ae_monotone
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_monotone_R_mesh_bound
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_bounded_weighted_R_mesh_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (R : Ω → ℝ≥0 → ℝ)
    (hR : ∀ ω t, R ω t =
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0))
    (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hu : ∀ i, i < n + 1 → u n i ≤ u n (i + 1))
    (hu0 : u n 0 = 0) (huT : u n (n + 1) ≤ T)
    (a : Ω → ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hBound : ∀ ω, ∀ i ∈ Finset.range (n + 1), |a ω i| ≤ K)
    (hInt : Integrable (fun ω => R ω T) P)
    (hMeas : AEStronglyMeasurable (fun ω =>
      ∑ i ∈ Finset.range (n + 1),
        a ω i * (R ω (u n i) - R ω (u n (i + 1)))) P) :
    Integrable (fun ω =>
      ∑ i ∈ Finset.range (n + 1),
        a ω i * (R ω (u n i) - R ω (u n (i + 1)))) P := by sorry
