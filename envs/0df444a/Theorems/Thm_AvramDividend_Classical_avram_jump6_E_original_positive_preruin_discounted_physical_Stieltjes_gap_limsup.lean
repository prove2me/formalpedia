-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_E_original_positive_preruin_discounted_physical_Stieltjes_gap_limsup
-- name    : AvramDividend.Classical.avram_jump6_E_original_positive_preruin_discounted_physical_Stieltjes_gap_limsup
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T19:13:04.850246+00:00
-- url     : https://prove2.me/theorems/60fab4ba-e54b-471d-ad16-d924bd06e1ef
-- title:
--   Strictly positive pre-ruin original canonical right-dividend Stieltjes mesh gap plus exact cash limsup nonpositive
-- statement:
--   For every strictly positive stopped σ(k) strictly before original ruin, with original mixed UBV Lévy and ν(Iio0)=∞, show exact canonical physical-mesh discounted rightLimit dividend W-gap plus time-zero atom plus inclusive Iic paymentTimes cash has nonpositive limsup. The original four-term full finite Ito/Source dividend correction cancels exactly by Proved c168c6c6, and its ruin contact conditional endpoint is absent on this strict event. This isolates the deterministic Stieltjes mesh/cash problem from the mixed stochastic source and can reuse Proved d44e536f pre-ruin discounted full cell domination, 0c66e93d discounted Stieltjes grid convergence, and 0b0c563c bounded stopped discounted mesh error. Retain original n, m(j), u(j,i), arbitrary stopped σ, right-payment atom at zero and C general positive.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_E_original_positive_preruin_discounted_physical_Stieltjes_gap_limsup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
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
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P)
    (hInfiniteActivity : X.ν (Iio (0 : ℝ)) = ⊤) :
    ∀ k : ℕ,
      let Cash : Ω → ℝ := fun ω : Ω =>
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
      let u : ℕ → ℕ → ℝ≥0 := fun j i =>
        (i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
      let m : ℕ → ℕ := fun j => (n + 1) * (j + 1)
      ∀ᵐ ω ∂P, (σ k ω ≠ 0 ∧
          (σ k ω : ℝ≥0∞) < ruinTime X x D ω) →
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ j in atTop,
            let v : ℕ → ℝ≥0 := fun i => min (u j i) (σ k ω)
            let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
            let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
            let Z : ℕ → ℝ := fun i =>
              x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
            (w (x - rightLimit D 0 ω) - w x) +
              (∑ i ∈ Finset.range (m j),
                E (v (i + 1)) * (w (Y (v (i + 1))) - w (Z i))) +
              Cash ω ≤ ε:= by sorry
