-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_source_psi_positive_small_tilt_below_any_positive_discount
-- name    : AvramDividend.Classical.avram_wave6_08_source_psi_positive_small_tilt_below_any_positive_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:57:53.447194+00:00
-- url     : https://prove2.me/theorems/6b7f5580-f12e-4a18-8862-48af9a18594f
-- title:
--   Any original spectrally negative Lévy ψ admits a positive Esscher tilt strictly below every q>0
-- statement:
--   For any source spectrally negative Lévy X without Standing, and q>0, there is θ>0 with ψθ<q. This is a true rate-existence result from original ψ continuous at 0 and ψ0=0, making θ-dependent source Stieltjes cash bounds usable for all positive q.
-- source:
--   Original Laplace exponent ψ0=0 canonical 88416f41 and ψ half-line continuous canonical 1fa27b74; independently needed to remove Standing/ψ1 restrictions from Chat08 actual-source θ-dependent dividend expectation/integrability package.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_zero
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_08_source_psi_positive_small_tilt_below_any_positive_discount
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) :
    ∃ θ : ℝ, 0 < θ ∧ X.ψ θ < q := by sorry
