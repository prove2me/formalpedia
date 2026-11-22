-- Prove2me | Theorems.Thm_AvramDividend_Classical_ripple_original_strict_preruin_full_discounted_Stieltjes_cash
-- name    : AvramDividend.Classical.ripple_original_strict_preruin_full_discounted_Stieltjes_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T16:57:16.877809+00:00
-- url     : https://prove2.me/theorems/a9c657c3-46b6-4e92-ae8d-5640767ea366
-- title:
--   Original strictly pre-ruin physical subclock, initial zero atom and exact discounted full Stieltjes dividend cash ledger
-- statement:
--   For the original spectrally negative Levy process and an actual admissible left-continuous dividend strategy, consider an arbitrary random physical subclock σ strictly earlier than the original ruin time. For every finite original clipped physical mesh v_i=min(iΔ,σ), retain the caplinear value V, after-right-dividend stopped reserve Y, frozen-dividend intermediate reserve Z, the original discounted Stieltjes dividendMeasure cash on each physical Ioc cell, the initial zero-time payment atom, and the exact time-discount commutator err. Prove pathwise that initial atom + discounted terminal V + cumulative actual cash is at most initial V + the true spatial frozen-dividend increments and discount errors. The per-cell strict pre-ruin survival assumptions previously needed are discharged directly from the single original stop σ<ruinTime. This is the source-faithful stopped finite-variation cash component of the original finite-cap Ito–Stieltjes estimate.
-- source:
--   Existing Proved original b252 stopped zero-atom full Stieltjes cash source 22281282-bbcb-4d12-b2c0-9aa782cd0035; actual finite-cap original positivepart source 0ef5d778-7536-4a04-90bc-68e0b5c21262. The original source still needs the strict/non-strict terminal-clock limit and its Brownian Ito Taylor errors.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b252_original_ruinclipped_precontact_zeroatom_and_full_Stieltjes_cash_source_ledger
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.ripple_original_strict_preruin_full_discounted_Stieltjes_cash
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
    (hStrict : (σ ω : ℝ≥0∞) < ruinTime X x D ω) :
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
    (∫⁻ t in Icc (0 : ℝ) (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω)).toReal +
      e m * V (Y m) + (Finset.range m).sum cash ≤
      V x +
      (Finset.range m).sum (fun i =>
        e (i + 1) * V (Z i) - e i * V (Y i)) +
      (Finset.range m).sum err := by sorry
