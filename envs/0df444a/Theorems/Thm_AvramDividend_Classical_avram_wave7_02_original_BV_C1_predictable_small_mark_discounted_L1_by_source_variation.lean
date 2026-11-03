-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_predictable_small_mark_discounted_L1_by_source_variation
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_C1_predictable_small_mark_discounted_L1_by_source_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:17:17.193288+00:00
-- url     : https://prove2.me/theorems/e6763634-2417-437d-9245-a4761aa78dca
-- title:
--   Original BV controlled predictable C1 small-jump discounted nonlinear difference bounded by physical negative source variation
-- statement:
--   On the original Levy controlled left-reserve path localised inside an actual positive strip [a,b], every negative original source mark of magnitude at most a/2 stays inside the C1 Lipschitz region. Its discounted nonlinear verification-function jump is bounded absolutely by L times the physical source-mark magnitude for nonnegative discount. This proves the exact pointwise domination needed for source finite-variation and predictable-mark integrability; no Ito identity or compensation assumption.
-- source:
--   Physical original left reserve and compact C1 Lipschitz estimate hLip, combined with source small-mark strip and bounded positive discount factor.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_C1_predictable_small_mark_discounted_L1_by_source_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (a b L : ℝ) (ha : 0 < a) (hab : a ≤ b) (hL : 0 ≤ L)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (ω : Ω) (t : ℝ≥0)
    (hBand : Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) t ∈ Icc a b)
    (z : ℝ) (hzSmall : -a / 2 ≤ z ∧ z ≤ 0) :
    |Real.exp (-(q * (t : ℝ))) *
      (w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t + z) -
      w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t))| ≤ L * |z| := by sorry
