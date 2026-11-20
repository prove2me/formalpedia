-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_positive_ruin_topcap_pathwise_physical_mesh_cash
-- name    : AvramDividend.Classical.avram_jump6_B_positive_ruin_topcap_pathwise_physical_mesh_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:38:05.775672+00:00
-- url     : https://prove2.me/theorems/94932179-01b6-41b4-8147-853a73222ea0
-- title:
--   Original true pathwise positive ruin-contact topcap finite physical grid signed cash
-- statement:
--   Pointwise at an actual positive ruin contact and finite top cap C=infinity, the original stopped signed discounted payment potential, true inclusive dividend cash and terminal ruin potential are dominated by the authentic mesh-error right dividend bound plus the shrinking pre-contact cash tail. Preserves the original stochastic Levy sample path, right-limit dividend book and crossing cell.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_positive_ruin_topcap_pathwise_physical_mesh_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hTop : C = ⊤)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (ρ : ℝ≥0)
    (hρpos : 0 < ρ) (hρruin : (ρ : ℝ≥0∞) = ruinTime X x D ω)
    (n : ℕ) (hn : 0 < n) (hρn : ρ ≤ (n : ℝ≥0)) (j : ℕ) :
    let v : ℕ → ℝ≥0 := fun i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ
    let m : ℕ := (n + 1) * (j + 1)
    let E : ℝ≥0 → ℝ := fun s => Real.exp (-(q * (s : ℝ)))
    let Y : ℝ≥0 → ℝ := fun s => x + X.X s ω - rightLimit D s ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    (w (x - rightLimit D 0 ω) - w x) +
      (∑ i ∈ Finset.range m,
        E (v (i + 1)) * (w (Y (v (i + 1))) - w (Z i))) +
      E ρ * (w (riskProcess X x D ρ ω) - w (Y ρ)) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ≤
      q * ((n : ℝ) / ((j : ℝ) + 1)) *
        Real.exp (q * (n : ℝ)) * rightLimit D ρ ω +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((ρ : ℝ) - (n : ℝ) / ((j : ℝ) + 1)) (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := by sorry
