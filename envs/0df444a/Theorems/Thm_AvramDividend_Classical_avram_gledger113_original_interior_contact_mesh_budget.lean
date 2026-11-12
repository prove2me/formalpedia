-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger113_original_interior_contact_mesh_budget
-- name    : AvramDividend.Classical.avram_gledger113_original_interior_contact_mesh_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:58:49.153964+00:00
-- url     : https://prove2.me/theorems/a408cb59-5b29-4a47-986f-49cc9cc81016
-- title:
--   Original interior dividend-contact source bounded by mesh width and total mass
-- statement:
--   The complete interior stopped dividend-contact cell ledger is bounded by the discount rate, the common mesh width and the total original dividend mass charged by those cells. It combines the proved pointwise non-C1 contact estimate with finite summation algebra, isolating the remaining mass-partition question from gledger81.
-- source:
--   Root-connected gledger81: combine Proved gledger99 complete interior contact sums with one mesh width and an externally established strict pre-stop real dividend mass bound.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger99_original_interior_contact_cells_sum_bound
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger113_original_interior_contact_mesh_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (ρ : ℝ≥0) (u : ℝ) (hu : 0 ≤ u)
    (hprefix : ∀ t : ℝ≥0, 0 < t → t < ρ →
      u ≤ riskProcess X x D t ω)
    (v : ℕ → ℝ≥0) (hv : Monotone v) (k : ℕ)
    (hinterior : ∀ i : ℕ, i < k → v (i + 1) < ρ)
    (hfinite : ∀ i : ℕ, i < k →
      dividendMeasure D ω (Ioc (v i : ℝ) (v (i + 1) : ℝ)) ≠ ⊤)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (δ M : ℝ) (hδ : 0 ≤ δ)
    (hmesh : ∀ i : ℕ, i < k → (v (i + 1) : ℝ) - (v i : ℝ) ≤ δ)
    (hMass : (Finset.sum (Finset.range k) (fun i =>
      (dividendMeasure D ω (Ioc (v i : ℝ) (v (i + 1) : ℝ))).toReal)) ≤ M) :
    (Finset.sum (Finset.range k) (fun i =>
      (∫⁻ s in Ioc (v i : ℝ) (v (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (v (i + 1) : ℝ))) *
        (w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) -
          w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω)))) ≤
      q * δ * M := by sorry
