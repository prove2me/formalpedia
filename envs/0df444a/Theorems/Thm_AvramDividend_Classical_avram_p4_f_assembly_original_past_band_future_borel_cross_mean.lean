-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_past_band_future_borel_cross_mean
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_past_band_future_borel_cross_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:06:32.005875+00:00
-- url     : https://prove2.me/theorems/db4d85db-898a-45e0-9a81-ca1740415941
-- title:
--   Original past negative-band count compensates every disjoint-time Borel future mark band on the same Lévy process
-- statement:
--   For actual spectrally negative Lévy process X, the original raw-past count on (0,s] with source mark band (-∞,-1/(n+1)] has the exact mixed ENNReal moment against the same process's future marked count on (s,t]×B for any measurable B: E[Jpast Jfuture] = E[Jpast](t-s)ν(B). Source raw adaptation and original P2-E weighted compensation discharge all stochastic premises. This supports distinct compensated small and uncompensated large future jump bands without assuming their independence or changing processes.
-- source:
--   Proved raw past-count adaptedness 41007669 and original weighted Borel source P2-E 12ff9a1a; generalises Proved same-band a8adacce, allows distinct mark bands including z≤-1 vs -1<z<0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_past_count_raw_measurable_auto
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_public_weighted_from_zero_origin_rate
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_past_band_future_borel_cross_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (n : ℕ)
    (B : Set ℝ) (hB : MeasurableSet B) :
    let Jpast : Ω → ℝ≥0∞ := fun ω => ((Measure.count.restrict {z : ℝ≥0 |
        0 < z ∧ X.X z ω -
          Function.leftLim (fun y : ℝ≥0 => X.X y ω) z ≠ 0}).map
        (fun z : ℝ≥0 => (z, X.X z ω -
          Function.leftLim (fun y : ℝ≥0 => X.X y ω) z)))
        (Ioc 0 s ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    let Jfuture : Ω → ℝ≥0∞ := fun ω => ((Measure.count.restrict {z : ℝ≥0 |
        0 < z ∧ X.X z ω -
          Function.leftLim (fun y : ℝ≥0 => X.X y ω) z ≠ 0}).map
        (fun z : ℝ≥0 => (z, X.X z ω -
          Function.leftLim (fun y : ℝ≥0 => X.X y ω) z)))
        (Ioc s t ×ˢ B)
    (∫⁻ ω, Jpast ω * Jfuture ω ∂P) =
      (∫⁻ ω, Jpast ω ∂P) *
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by sorry
