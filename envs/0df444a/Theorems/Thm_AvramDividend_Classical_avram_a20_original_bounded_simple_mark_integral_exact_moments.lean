-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_bounded_simple_mark_integral_exact_moments
-- name    : AvramDividend.Classical.avram_a20_original_bounded_simple_mark_integral_exact_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:16:09.437282+00:00
-- url     : https://prove2.me/theorems/f7943aaa-490a-4d0e-a38b-7d56f87e8da1
-- title:
--   Exact integrability, raw first moment and raw second moment of a true original bounded finite-valued negative jump-mark integral
-- statement:
--   For the actual original spectrally negative Lévy process with finite negative activity and a measurable negative Borel band S, every uniformly unit-bounded finite-valued measurable real mark g has a genuine original physical marked-jump real integral J=∫_(0,T]×S g(z)dNX with integrable square and exact first and second raw moments. Its mean m is the finite sum over mark values y of y Tν(S∩g^{-1}({y})); its raw square moment is m²+v, where v is the corresponding sum of y² Tν(cell). The direct proof uses the authoritative Proved original finite-valued weighted Borel partition count moments, almost sure finite total original negative jump count, the Proved bounded physical marked-integral integrability, and the exact real simple-mark integral-to-count identity. A.e. equality transfers integrability and both exact moments. This closes the finite-valued physical integral stage of JA28 without auxiliary Poisson noise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_bounded_simple_mark_integral_exact_moments
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Set ℝ) (hS : MeasurableSet S)
    (hNeg : S ⊆ Iio (0 : ℝ))
    (g : SimpleFunc ℝ ℝ)
    (hBound : ∀ z ∈ S, |g z| ≤ 1) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
    let J : Ω → ℝ := fun ω =>
      ∫ p in (Ioc 0 T ×ˢ S), g p.2 ∂NX ω
    let m : ℝ := ∑ y ∈ g.range,
      y * (((T : ℝ≥0∞) * X.ν (B y)).toReal)
    let v : ℝ := ∑ y ∈ g.range,
      y ^ 2 * (((T : ℝ≥0∞) * X.ν (B y)).toReal)
    Integrable J P ∧ Integrable (fun ω => J ω ^ 2) P ∧
      (∫ ω, J ω ∂P) = m ∧
      (∫ ω, J ω ^ 2 ∂P) = m ^ 2 + v := by sorry
