-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys60_original_finitecap_uniform_strict_cash_terminal_envelope
-- name    : AvramDividend.Classical.avram_bvb_phys60_original_finitecap_uniform_strict_cash_terminal_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T18:25:07.677407+00:00
-- url     : https://prove2.me/theorems/51874677-8c4a-4196-bd6a-6627c8165504
-- title:
--   Original finite-cap strict cash and surviving terminal have a common integrable envelope
-- statement:
--   For each original bounded refining-grid clock T-T/(n+2), dominate the physical strict pre-ruin dividend cash by the full fixed-horizon discounted cash from proved e0aebc07, and the surviving terminal by the deterministic finite-cap candidate envelope using proved c521fe8f and df040a51. Choose K equal to the integrable full cash plus an explicit cap constant. This is a necessary and sound cash component for physical-source majorant 524afc4a.
-- source:
--   Original BV physical finite-activity source route, needed for 524afc4a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys60_original_finitecap_uniform_strict_cash_terminal_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∃ K : Ω → ℝ, Integrable K P ∧
      ∀ n : ℕ, ∀ ω : Ω, F n ω ≤ K ω := by sorry
