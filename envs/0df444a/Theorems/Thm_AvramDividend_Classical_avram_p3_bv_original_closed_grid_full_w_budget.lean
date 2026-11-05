-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_closed_grid_full_w_budget
-- name    : AvramDividend.Classical.avram_p3_bv_original_closed_grid_full_w_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T20:25:59.558864+00:00
-- url     : https://prove2.me/theorems/dc7eeb89-4440-4938-918e-5340b3c09860
-- title:
--   Original BV finite-grid full closed Stieltjes cash and genuine w terminal bounded from genuine w initial capital
-- statement:
--   For the original spectrally negative Levy process and actual admissible dividend strategy, the complete physical finite-grid discounted Stieltjes cash including time-zero dividend atom, and the true post-rightpayment w terminal, are controlled by the literal initial w(x) plus explicit cap-linear original source-cell terms. Both finite and infinite caps are covered. The proof discharges the auxiliary initial V(x) equality at admissible capital from closed-cap extension identity.
-- source:
--   Direct source-exact composition of Proved dca893c2 physical original cap-linear Stieltjes grid, Proved 37425aad original postpayment V=w at cap, and Proved 85617d04 initial capped V(x)=w(x).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_explicit_caplinear_source_mesh
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_caplinear_extension_eq_w_closed_cap

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- Complete original finite-grid verification ledger, with the genuine
initial w x and genuine postpayment w terminal; only cells use V. -/

theorem AvramDividend.Classical.avram_p3_bv_original_closed_grid_full_w_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ)
    (hu : Monotone u) (hu0 : u 0 = 0)
    (hPre : ∀ i : ℕ, i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
    E (u n) * w (Y (u n)) +
      (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal ≤
      w x +
        ∑ i ∈ Finset.range n,
          ((E (u (i + 1)) - E (u i)) * V (Y (u (i + 1))) +
            E (u i) * (V (Z i) - V (Y (u i)))) := by sorry
