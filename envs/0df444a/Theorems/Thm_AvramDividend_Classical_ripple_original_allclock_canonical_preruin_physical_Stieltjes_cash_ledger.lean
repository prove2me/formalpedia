-- Prove2me | Theorems.Thm_AvramDividend_Classical_ripple_original_allclock_canonical_preruin_physical_Stieltjes_cash_ledger
-- name    : AvramDividend.Classical.ripple_original_allclock_canonical_preruin_physical_Stieltjes_cash_ledger
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:26:20.614788+00:00
-- url     : https://prove2.me/theorems/13bb448f-dc04-4253-aa8d-0f0c00387897
-- title:
--   Actual original positive ruin-clipped random clock admits the full finite-grid discounted caplinear Stieltjes cash ledger on every canonical strict subclock
-- statement:
--   For the original spectrally negative Levy reserve, finite or infinite dividend cap, and true admissible left-continuous dividend strategy, assume only an actual positive random stopping clock no later than original ruin. At every positive natural mesh index j, replace that clock by its canonical physical time strictly before it: sigma minus sigma divided by j plus one. Prove the full original finite-grid stopped discounted Ito-Stieltjes dividend cash ledger at this canonical subclock, retaining the actual original initial zero-time Stieltjes payment atom, physical stopped post-right-dividend terminal reserve, original caplinear potential, exact real dividendMeasure Ioc cell cash, frozen-dividend original spatial increments and discount commutator. This is a genuine source-faithful bridge from the full original nonstrict ruin-clipped clock hypothesis to the proved pre-ruin cash ledger, without hypothetical cash inequalities or any assumption that canonical subclock is a stopping time. Passing to original prepayment terminal requires the separate proved original cofinal cash limit.
-- source:
--   Proved actual original strict-survival cash ledger a9c657c3-46b6-4e92-ae8d-5640767ea366 and cofinal prepayment cash bbe7e6a0-afc6-441d-9d3d-7a29d53e1993; original finitecap physical source 0ef5d778-7536-4a04-90bc-68e0b5c21262.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ripple_original_strict_preruin_full_discounted_Stieltjes_cash
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.ripple_original_allclock_canonical_preruin_physical_Stieltjes_cash_ledger
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
    (hσpos : 0 < σ ω)
    (hσle : (σ ω : ℝ≥0∞) ≤ ruinTime X x D ω) (j : ℕ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (σ ω - σ ω / ((j : ℝ≥0) + 1))
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
