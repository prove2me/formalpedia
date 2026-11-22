-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_original_prepost_gradient_discounted_atom_grid_domination
-- name    : AvramDividend.Classical.avram_lsv_original_prepost_gradient_discounted_atom_grid_domination
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T21:41:43.300389+00:00
-- url     : https://prove2.me/theorems/6470cf62-f3a3-4806-ac32-bff3e9a33723
-- title:
--   Original Gaussian pre/post gradient cost dominated by the physical discounted rightdividend Gaussian mesh
-- statement:
--   For the exact original Avram top-cap Gaussian source and original strictly pre-ruin compact prefix, there exists a mesh-independent constant L such that the true derivative-difference first Hermite error is integrable and its expected value is bounded by L times the original discounted right dividend atom weighted absolute Gaussian increment mesh. Requires compact gradient Lipschitz bounds, initial time treatment, and right-limit band. No prior assumption of square root mesh convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_lsv_original_prepost_gradient_discounted_atom_grid_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let Elinear : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let Z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        let U := Z ^ 2 - (Δ : ℝ) * X.σ ^ 2
        let ypost := x + X.X s ω - rightLimit D s ω
        let ypre := riskProcess X x D s ω
        let e : ℝ := if s < ρ ω then Real.exp (-(q * (s : ℝ))) else 0
        |e| * |deriv w ypost - deriv w ypre| * |Z|
    let V : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let H : ℝ := if s < ρ ω then
          Real.exp (-(q * (s : ℝ))) *
            (rightLimit D s ω - D s ω)
          else 0
        let Z : ℝ := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        H * |Z|
    ∃ L : ℝ, 0 ≤ L ∧ ∀ m : ℕ,
      Integrable (Elinear m) P ∧
        (∫ ω, Elinear m ω ∂P) ≤
          L * (∫ ω, V m ω ∂P) := by sorry
