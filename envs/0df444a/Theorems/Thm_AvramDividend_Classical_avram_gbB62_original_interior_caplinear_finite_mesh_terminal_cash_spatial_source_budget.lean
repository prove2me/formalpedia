-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB62_original_interior_caplinear_finite_mesh_terminal_cash_spatial_source_budget
-- name    : AvramDividend.Classical.avram_gbB62_original_interior_caplinear_finite_mesh_terminal_cash_spatial_source_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:56:49.097504+00:00
-- url     : https://prove2.me/theorems/4e905b17-a74e-46a6-99fc-e236d9c1c364
-- title:
--   Original interior-clipped finite physical-grid stopped terminal cash is bounded by the source spatial increments
-- statement:
--   For the original Lévy source X and admissible dividend D, the actual discounted Stieltjes cash increments over finite monotone strictly pre-ruin physical grid, plus the original initial right dividend atom and the terminal postpayment caplinear value, are bounded by initial caplinear value plus the sum of actual prepayment-at-start source spatial potential differences. This telescopes the source-faithful initial atom and signed Stieltjes corrections without changing original admissibility cap C or identifying D with rightLimit D. This is a rigorous finite-mesh cash source component for B54; Gaussian C2 source and stop-straddling error still remain.
-- source:
--   The original signed finite-grid dividend plus initial atom inequality B60, original source exact reserve relation X.X0=0 and B61 purely algebraic finite-grid potential telescoping.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB60_original_interior_clipped_finite_mesh_cash_and_initial_atom_budget
import Theorems.Thm_AvramDividend_Classical_avram_gbB61_finite_mesh_postpayment_potential_cash_telescope
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_gbB62_original_interior_caplinear_finite_mesh_terminal_cash_spatial_source_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (C : ℝ≥0∞)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (hV : ∀ z : ℝ, V z =
      if z ≤ c then w z else w c + (z - c))
    (hsec : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ c →
      t - s ≤ w t - w s)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ)
    (hPre : ∀ i < n, u (i + 1) = 0 ∨
      (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
    (hu0 : u 0 = 0) :
    let Y : ℕ → ℝ := fun i =>
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
    let Z : ℕ → ℝ := fun i =>
      V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω)
    let Cash : ℕ → ℝ := fun i =>
      (∫⁻ s in Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
    rightLimit D 0 ω + Y n + (Finset.sum (Finset.range n) (fun i => Cash i)) ≤
      V x + (Finset.sum (Finset.range n) (fun i => Z i - Y i)) := by sorry
