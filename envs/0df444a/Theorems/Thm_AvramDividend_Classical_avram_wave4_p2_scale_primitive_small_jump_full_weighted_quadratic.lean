-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_small_jump_full_weighted_quadratic
-- name    : AvramDividend.Classical.avram_wave4_p2_scale_primitive_small_jump_full_weighted_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:38:21.022+00:00
-- url     : https://prove2.me/theorems/e71795d5-c768-461d-8896-2d8853964932
-- title:
--   Actual original primitive small-jump kernel has global weighted O(r²) positive-reserve mass
-- statement:
--   For the genuine source scale primitive U and original negative-jump Lévy generator integrand, at every 0<r<1 its exponentially weighted absolute positive-reserve x-section is integrable and bounded by r² times (W(1) plus one half the global weighted absolute scale derivative mass). Both terms are finite under standing and θ≥0,q<ψθ. This is exactly the quadratic small-jump Fubini domination missing for non-Gaussian infinite variation; it imports the Proved actual crossing and interior section estimates f587f475 and c0fb07f0 and uses only disjoint strip integral decomposition. It does not yet assert integrability over the Lévy measure or interchange the two integrations.
-- source:
--   Avram Palmowski Pistorius 2007, Lemma 4; canonical actual source compensated crossing and interior weighted estimates; Mathlib setIntegral_union and integral_Ici_eq_integral_Ioi.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p2_scale_primitive_small_jump_full_weighted_quadratic
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (r θ : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(θ*x)) *
        |SpectrallyNegativeLevy.generatorIntegrand
          (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x (-r)|)
      (Ioi (0 : ℝ)) volume ∧
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) *
      |SpectrallyNegativeLevy.generatorIntegrand
        (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x (-r)|) ≤
      W 1 * r^2 + (r^2/2) * (∫ u : ℝ, Real.exp (-θ*u) *
        |(Ioi (0 : ℝ)).indicator (deriv W) u|) := by sorry
