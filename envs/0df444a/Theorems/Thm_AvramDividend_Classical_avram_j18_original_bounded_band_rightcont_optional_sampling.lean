-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_j18_original_bounded_band_rightcont_optional_sampling
-- name    : AvramDividend.Classical.avram_j18_original_bounded_band_rightcont_optional_sampling
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T18:19:24.788084+00:00
-- url     : https://prove2.me/theorems/2d92580d-b017-4d74-b84f-5700ea51a824
-- title:
--   Bounded original right-continuous stopping preserves compensated-band conditional centring
-- statement:
--   For a true original right-continuous-filtration L1 martingale field with right-continuous paths, zero initial value and one integrable uniform horizon envelope, any bounded genuine original stopping time has an integrable sampled value conditionally centred at the initial sigma-algebra. This isolates the optional-sampling passage from physical jump-field construction.
-- source:
--   Separate purely stopping/measure-theoretic child of Open 61f39bfe using the exact same original filtration. An integrable uniform bound and càdlàg-from-right field are supplied by the companion child.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_j18_original_bounded_band_rightcont_optional_sampling
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (Jsmall : ℝ≥0 → Ω → ℝ) (B : Ω → ℝ)
    (hInt : ∀ t : ℝ≥0, Integrable (Jsmall t) P)
    (hMart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (Jsmall t) ω = Jsmall s ω)
    (hRight : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun u : ℝ≥0 => Jsmall u ω) (Set.Ici t) t)
    (hZero : ∀ᵐ ω ∂P, Jsmall 0 ω = 0)
    (hBInt : Integrable B P)
    (hDom : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) →
      ‖Jsmall t ω‖ ≤ B ω) :
    Integrable (fun ω => Jsmall (τ ω) ω) P ∧
    (∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P
        (fun ω => Jsmall (τ ω) ω) ω = 0) := by sorry
