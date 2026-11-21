-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_original_fullnegative_physical_finite_horizon_count_L1
-- name    : AvramDividend.Classical.avram_freshD_original_fullnegative_physical_finite_horizon_count_L1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:50:56.239204+00:00
-- url     : https://prove2.me/theorems/e19df3d9-f75c-4567-8369-b45f30985076
-- title:
--   Original finite-activity full-negative Lévy physical count on deterministic finite horizon is L1
-- statement:
--   For the genuine original spectrally negative Lévy jump count NX, finite negative-jump intensity on (-∞,0) implies that the real-valued total number of negative jumps on physical time (0,n] is integrable. The proof constructs an almost-sure measurable integer-valued count realisation and derives L1 from the already proved original finite-activity second moment by elementary domination 0≤N≤N²+1. This is the actual Poisson-count integrable majorant needed to bound all negative-marked physical mesh cells and pass their small-modulus errors to zero in the original mixed stopped Itô–Stieltjes comparison.
-- source:
--   Original physical fullnegative mark counting source for Avram Dividend Classical root via positive-excess 242ca5f1; finite ν activity, Proved a6562a4d negative count L2 and Proved 84a4791e count Borel-realisation; avoids assuming any expected stopped cash or false linear mark formula.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_anoise18_original_total_negative_count_finite_activity_L2
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_nat_count_realisation
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_freshD_original_fullnegative_physical_finite_horizon_count_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t,
          X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
    let N : Ω → ℝ := fun ω =>
      ((NX ω) (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ))).toReal
    Integrable N P := by sorry
