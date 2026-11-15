-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b248_original_ruinclipped_precontact_physical_full_Stieltjes_cash_source_ledger
-- name    : AvramDividend.Classical.avram_b248_original_ruinclipped_precontact_physical_full_Stieltjes_cash_source_ledger
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:31:07.046258+00:00
-- url     : https://prove2.me/theorems/b5747812-5779-445b-b3a1-26287f63f115
-- title:
--   Original ruin-clipped all-cap precontact stopped physical-grid full discounted Stieltjes cash bounded by true Lévy spatial source plus explicit discount mismatch
-- statement:
--   On any true physically stopped finite grid v_i=min(iΔ,σ(ω)) whose complete cells end before ruin, the genuine original full Stieltjes discounted dividend cash on (v_i,v_{i+1}] plus the discounted terminal post-right-dividend caplinear potential is bounded by the initial true postpayment potential plus all original Lévy frozen-right-dividend spatial source increments and an explicit sum of left-to-right within-cell discount mismatch terms. This exact pathwise source-faithful inequality preserves original cap C, actual Lévy X and D, true stopped grid, all continuous and atomic dividend cash in each cell, and distinguishes the separate ruin-straddling final cell and time-zero atom. It is a key signed Itô cash ledger step for B236.
-- source:
--   Sum Proved B241 original allcap frozen-source full discounted Stieltjes cell inequalities, and invoke Proved B238 exact original stopped spatial/postpayment discount telescope. Simple finite algebra isolates true cash and terminal from the source and discount mismatch. Stopping at all precontact grid cells avoids assumptions on the unknown post-ruin path.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b238_original_ruinclipped_finiteactivity_physical_stopped_source_postdividend_telescope
import Theorems.Thm_AvramDividend_Classical_avram_b241_original_ruinclipped_allcap_physical_cash_left_to_right_discount_mesh_correction
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b248_original_ruinclipped_precontact_physical_full_Stieltjes_cash_source_ledger
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0) (n m : ℕ) (ω : Ω)
    (hPre : ∀ i ∈ Finset.range m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun j => min ((j : ℝ≥0) * Δ) (σ ω)
      v (i + 1) = 0 ∨
        (v (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (σ ω)
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (v i : ℝ)))
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else
      if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    let Y : ℕ → ℝ := fun i =>
      x + X.X (v i) ω - rightLimit D (v i) ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in Ioc (v i : ℝ) (v (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal
    let err : ℕ → ℝ := fun i =>
      (e i - e (i + 1)) * (V (Z i) - V (Y (i + 1)))
    e m * V (Y m) + (Finset.range m).sum cash ≤
      e 0 * V (Y 0) +
      (Finset.range m).sum (fun i =>
        e (i + 1) * V (Z i) - e i * V (Y i)) +
      (Finset.range m).sum err := by sorry
