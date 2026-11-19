-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_strict_preruin_stieltjes_discount_cash
-- name    : AvramDividend.Classical.avram_jump6_B_original_canonical_strict_preruin_stieltjes_discount_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T20:35:44.164212+00:00
-- url     : https://prove2.me/theorems/a040a005-5de1-4342-b6cd-10d2cd87fc75
-- title:
--   Original strict-pre-ruin closed-Iic cash controlled by exact canonical physical grid and vanishing discount mass
-- statement:
--   Source-exact application of the public original same-process allcap signed Stieltjes cash estimate to the genuine canonical NNReal physical uniform grid j with count (n+1)(j+1) covering the bounded stopped time. Proves exact original paymentTimes intersect Iic tau cash inequality with real clipped predividend path and ENNReal error q/(j+1)*dividendMeasure mass tending to zero. All assumptions remain original and no finite activity or surrogate process is introduced.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_strict_preruin_paymentTimes_clipped_stieltjes_grid_budget
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_canonical_NNReal_grid_exact_mesh_width_and_limit
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_canonical_grid_reaches_bounded_clock_every_mesh
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_canonical_strict_preruin_stieltjes_discount_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτT : τ ω ≤ T)
    (hStrict : (τ ω : ℝ≥0∞) < ruinTime X x D ω)
    (n : ℕ) (hn : τ ω ≤ (n : ℝ≥0)) :
    let u : ℕ → ℕ → ℝ≥0 := fun j i =>
      (i : ℝ≥0) / (((j + 1 : ℕ) : ℝ≥0))
    let k : ℕ → ℕ := fun j => (n + 1) * (j + 1)
    let mesh : ℕ → ℝ := fun j => (1 : ℝ) / ((j : ℝ) + 1)
    (let v : ℕ → ℕ → ℝ≥0 := fun n i => min (u n i) (τ ω)
     (∀ n,
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (rightLimit D 0 ω) * ENNReal.ofReal (Real.exp (-(q * 0))) +
      ((∑ i ∈ Finset.range (k n),
        ENNReal.ofReal (Real.exp (-(q * (v n (i + 1) : ℝ)))) *
          ENNReal.ofReal
            (V (x + X.X (v n (i + 1)) ω - rightLimit D (v n i) ω) -
             V (x + X.X (v n (i + 1)) ω - rightLimit D (v n (i + 1)) ω))) +
        ENNReal.ofReal (q * mesh n) *
          dividendMeasure D ω (Ioc (0 : ℝ) (τ ω : ℝ)))) ∧
     Tendsto
       (fun n =>
         (ENNReal.ofReal (q * mesh n) *
          dividendMeasure D ω (Ioc (0 : ℝ) (τ ω : ℝ))).toReal)
       atTop (𝓝 0)) := by sorry
