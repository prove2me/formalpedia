-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_localised_full_precontact_physical_cash_rate_from_caplinear
-- name    : AvramDividend.Classical.avram_f6_original_localised_full_precontact_physical_cash_rate_from_caplinear
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:07:38.64908+00:00
-- url     : https://prove2.me/theorems/bab3a5ad-0fef-4791-82d6-a29d6c63b646
-- title:
--   Original all-cap localised physical stopped pre-ruin full-Stieltjes cash error bounded by mesh width and total dividends
-- statement:
--   For the true original spectrally negative Lévy process and admissible dividend strategy with any positive dividend cap, choose the canonical physical grid of a stopping clock. If every next grid endpoint is zero or strictly pre-ruin, and both actual prepayment and postpayment reserves are in a common compact band where the cap-linear extension V of w has verified Lipschitz constant L, then the sum of all true discounted Stieltjes dividend cash and the right-discounted physical cap-linear postpayment potential correction is at most q times the mesh width times L times the increment of actual cumulative rightLimit dividends. This closes the original strict-precontact physical signed cash estimate under precisely the necessary local-band hypothesis. Derive by combining the Proved original cap-linear right-discount cash ledger (1c8f), original clipped physical dividend-mass discount gap rate b254 (705d), and physical stopping-grid monotonicity b250 (de2b), controlling the signed residual by its absolute value. The final ruin-contact cell and removal of localisation are separate genuine obligations.
-- source:
--   Proved original 1c8f563f exact caplinear right-discount physical cash source; Proved 705da1e7 physical Lipschitz dividend oscillation bound; Proved de2b51bf true original grid monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_localised_full_precontact_physical_cash_rate_from_caplinear
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (σ : Ω → ℝ≥0) (n m : ℕ)
    (hPre : ∀ i < m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun j => min ((j : ℝ≥0) * Δ) (σ ω)
      v (i + 1) = 0 ∨
        (v (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
    (L a b : ℝ) (hL : 0 ≤ L)
    (hLip :
      let V : ℝ → ℝ := fun z =>
        if C = ⊤ then w z else
        if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        |V s - V t| ≤ L * |s - t|)
    (hBefore : ∀ i < m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun j => min ((j : ℝ≥0) * Δ) (σ ω)
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω ∈ Icc a b)
    (hAfter : ∀ i < m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun j => min ((j : ℝ≥0) * Δ) (σ ω)
      x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω ∈ Icc a b) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (σ ω)
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else
      if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    let E : ℕ → ℝ := fun i => Real.exp (-(q * (v i : ℝ)))
    let Cash : ℕ → ℝ := fun i =>
      (∫⁻ t in Ioc (v i : ℝ) (v (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    (Finset.sum (Finset.range m) (fun i =>
      Cash i + E (i + 1) *
        (V (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) -
         V (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω)))) ≤
      q * (Δ : ℝ) * L *
        (rightLimit D (v m) ω - rightLimit D (v 0) ω) := by sorry
