-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_generatorIntegrand_interior_weighted_quadratic
-- name    : AvramDividend.Classical.avram_wave4_p2_scale_primitive_generatorIntegrand_interior_weighted_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:13:31.792371+00:00
-- url     : https://prove2.me/theorems/c0fb07f0-3873-42f0-bcbf-4e0588af907d
-- title:
--   Actual source primitive interior generator kernel has O(r²) weighted L1
-- statement:
--   For each true small negative jump -r with 0<r<1, the original source generatorIntegrand of the scale primitive is absolutely integrable against exponentially weighted reserves x>r, and the integral is bounded by r²/2 times the global weighted absolute integral of source scale derivative. This is the exact source-specific interior half of the finite quadratic small-jump Fubini estimate; the crossing strip bound is already canonically Proved as 5becd970. The proof imports source curvature L1 1c8cfca2, exact source tent 7047e205, and generic tent e11ef020.
-- source:
--   Avram Palmowski Pistorius 2007, Lemma 4 and pinned canonical weighted kernel e11ef020; no harmonicity assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p2_scale_primitive_generatorIntegrand_interior_weighted_quadratic
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (r θ : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-θ*x) *
        |SpectrallyNegativeLevy.generatorIntegrand
          (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x (-r)|)
      (Ioi r) volume ∧
    (∫ x in Ioi r, Real.exp (-θ*x) *
      |SpectrallyNegativeLevy.generatorIntegrand
        (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x (-r)|) ≤
      (r^2/2) * (∫ u : ℝ, Real.exp (-θ*u) *
        |(Ioi (0 : ℝ)).indicator (deriv W) u|) := by sorry
