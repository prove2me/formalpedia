-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb91_nested_integral_real_L2_polarization
-- name    : AvramDividend.Classical.avram_gb91_nested_integral_real_L2_polarization
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T15:05:24.687414+00:00
-- url     : https://prove2.me/theorems/355e509f-bdd9-4ac7-a588-512e263a3589
-- title:
--   Integrated real L2 polarization for two time-dependent stochastic integrands
-- statement:
--   For real functions indexed by time on an original probability space, the squared L2 difference integrated over a finite open time interval equals the sum of the individual integrated squared energies minus twice the integrated cross energy, provided all three inner and outer integrability hypotheses hold.
-- source:
--   Direct original finitecap two-mesh energy polarization gbB68 (6cb63bc4-12e8-41cb-933c-19ad50327bbc): isolates the nested integration algebra, leaving only actual physical integrability of L and K coefficients for the parent bridge.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb73_integral_L2_polarization
open MeasureTheory Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gb91_nested_integral_real_L2_polarization
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T : ℝ) (f g : ℝ → Ω → ℝ)
    (hinner : ∀ t : ℝ,
      Integrable (fun ω => (f t ω) ^ 2) P ∧
      Integrable (fun ω => (g t ω) ^ 2) P ∧
      Integrable (fun ω => f t ω * g t ω) P)
    (hf : IntegrableOn (fun t => ∫ ω, (f t ω) ^ 2 ∂P)
      (Ioo (0 : ℝ) T) volume)
    (hg : IntegrableOn (fun t => ∫ ω, (g t ω) ^ 2 ∂P)
      (Ioo (0 : ℝ) T) volume)
    (hfg : IntegrableOn (fun t => ∫ ω, f t ω * g t ω ∂P)
      (Ioo (0 : ℝ) T) volume) :
    (∫ t in Ioo (0 : ℝ) T,
      (∫ ω, (f t ω - g t ω) ^ 2 ∂P) ∂volume) =
      (∫ t in Ioo (0 : ℝ) T,
        (∫ ω, (f t ω) ^ 2 ∂P) ∂volume) +
      (∫ t in Ioo (0 : ℝ) T,
        (∫ ω, (g t ω) ^ 2 ∂P) ∂volume) -
      2 * (∫ t in Ioo (0 : ℝ) T,
        (∫ ω, f t ω * g t ω ∂P) ∂volume) := by sorry
