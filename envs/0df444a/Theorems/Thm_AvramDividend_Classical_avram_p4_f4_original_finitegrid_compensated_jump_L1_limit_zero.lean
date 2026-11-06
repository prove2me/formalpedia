-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_finitegrid_compensated_jump_L1_limit_zero
-- name    : AvramDividend.Classical.avram_p4_f4_original_finitegrid_compensated_jump_L1_limit_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:07:04.036772+00:00
-- url     : https://prove2.me/theorems/a907358c-0be1-418d-b594-6a8b3599573d
-- title:
--   Actual original compensated negative-jump finite-grid stochastic sums preserve zero mean in L1 limit
-- statement:
--   For the original right-continuous Lévy negative jump counting map with finite-band compensation, predictable L2 weights, and exact finite-grid sources, the stochastic sums are centred. If they converge in L1 to an integrable physical stopped jump martingale, that limit also has zero expectation.
-- source:
--   Original finite-grid physical jump zero-mean and L1 centred-limit bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_finite_grid_zero_mean_from_source_rate
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped ENNReal NNReal Nat BigOperators
noncomputable section
noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_original_finitegrid_compensated_jump_L1_limit_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (ε : ℝ) (hε : 0 < ε) (C : ℕ → Set ℝ)
    (hC : ∀ i, MeasurableSet (C i))
    (hBand : ∀ i, C i ⊆ Ioo (-1 : ℝ) (-ε))
    (hν : ∀ i, X.ν (C i) < ⊤)
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ C i))
    (hMeas : ∀ i, Measurable (N i))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (hCountL2 : ∀ i, MemLp (fun ω =>
      (N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C i)).toReal) 2 P)
    (M : Ω → ℝ) (hMI : Integrable M P)
    (hConv : Filter.Tendsto
      (fun n => ∫⁻ ω, ‖(∑ i ∈ Finset.range n,
        H i ω *
          ((N i ω).toReal -
            (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
              X.ν (C i)).toReal)) - M ω‖ₑ ∂P)
      atTop (𝓝 0)) :
    (∫ ω, M ω ∂P) = 0 := by sorry
