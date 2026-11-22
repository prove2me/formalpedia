-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_killed_scale_window_setIntegral_identity_no_standing
-- name    : AvramDividend.Classical.p2m81_bv_killed_scale_window_setIntegral_identity_no_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T05:10:32.258958+00:00
-- url     : https://prove2.me/theorems/b68c581e-015f-4ef7-962f-c73b13b8a9be
-- title:
--   BV killed scale future-window set-integral identity from Esscher root without standing (public)
-- statement:
--   For a bounded-variation spectrally negative Levy process with positive discount q, positive Esscher root phi with psi(phi)=q, genuine q-scale function W, integrable future-window payoff and fixed-time scale values, and the scalar whole-path identity over a covering schedule, the set integrals of the killed payoff and the scale value agree on every past-measurable set A. No Standing assumption.
-- source:
--   Condexp-assembly half of the no-standing mirror of Proved c2e577be: pointwise kernel identity via sibling H1c2, renewal kernel via standing-free Proved 8c2d238f, ennreal/real transfer via ofReal_integral_eq_lintegral_ofReal. Discharges the per-set goal of parent H1 (ee75bf61).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.p2m81_bv_killed_scale_window_setIntegral_identity_no_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation) (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) (T : ℝ≥0)
    (τ : ℕ → ℝ≥0) (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ, ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = T) (hT : s + T = u) (hTc : (T : ℝ) = (u : ℝ) - (s : ℝ))
    (hEvent : ∀ ω : Ω, (∀ v : ℝ≥0, v ≤ T →
      0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)) ↔ ω ∈
      {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)})
    (hf : Integrable (({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
      0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
      (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
        W (x + X.X u ω))) P)
    (hg : Integrable (fun ω => W (x + X.X s ω)) P)
    (hf0 : ∀ ω : Ω, 0 ≤ (({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
      0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
      (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
        W (x + X.X u ω))) ω)
    (hg0 : ∀ ω : Ω, 0 ≤ W (x + X.X s ω))
    (hScalar : ∀ h : ℝ,
      (∫⁻ z : ℝ≥0 → ℝ,
        if ∀ j : ℕ, τ j ≤ T → 0 ≤ h + z (τ j) then
          ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) * W (h + z T))
        else (0 : ℝ≥0∞)
        ∂(Measure.map (fun ω : Ω => (fun t : ℝ≥0 => X.X t ω)) P)) =
      ENNReal.ofReal (W h))
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    (∫ ω, A.indicator (({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
      0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
      (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
        W (x + X.X u ω))) ω ∂P) =
    ∫ ω, A.indicator (fun ω => W (x + X.X s ω)) ω ∂P := by sorry
