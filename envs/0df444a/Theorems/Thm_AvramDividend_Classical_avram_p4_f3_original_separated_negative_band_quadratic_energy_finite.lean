-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_separated_negative_band_quadratic_energy_finite
-- name    : AvramDividend.Classical.avram_p4_f3_original_separated_negative_band_quadratic_energy_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:00:51.061891+00:00
-- url     : https://prove2.me/theorems/5defbca2-1a88-40c4-bec9-a5b6f56185a7
-- title:
--   Original finite-intensity large negative-jump band has finite physical L2 coefficient energy
-- statement:
--   The original spectrally negative Lévy source X has finite quadratic physical Lévy measure energy for each canonical value jump coefficient w(u+z)-w(u) on a negative Borel band separated from zero, uniformly in every finite upper reserve ceiling u≤K. This combines the proved source value envelope and original ν finite-band rate without independent processes or unjustified integrability.
-- source:
--   From the Proved P4-F3 original negative-band quadratic kernel lintegral envelope c3b03f14 and Proved P2 original separated Borel Lévy measure finiteness 86086cb2, conclude physical band quadratic energy <top using pinned ENNReal.mul_lt_top and ofReal_lt_top. Dependency c3b03f14 must be Proved before authoring; no circular import of canonical source fdb or residual 0dda.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_band_squared_kernel_lintegral_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original separated negative-band quadratic jump energy is finite at every bounded reserve level. -/

theorem AvramDividend.Classical.avram_p4_f3_original_separated_negative_band_quadratic_energy_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (K : ℝ) (hK : 0 ≤ K)
    (ε : ℝ) (hε : 0 < ε)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hBsep : B ⊆ Iic (-ε)) :
    ∀ u : ℝ, u ≤ K →
      (∫⁻ z in B, ENNReal.ofReal ((w (u + z) - w u) ^ 2) ∂X.ν) < ⊤ := by sorry
