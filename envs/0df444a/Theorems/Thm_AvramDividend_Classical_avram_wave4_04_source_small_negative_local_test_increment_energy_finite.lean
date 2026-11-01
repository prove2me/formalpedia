-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04_source_small_negative_local_test_increment_energy_finite
-- name    : AvramDividend.Classical.avram_wave4_04_source_small_negative_local_test_increment_energy_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:24:13.307255+00:00
-- url     : https://prove2.me/theorems/42056f54-e990-45d6-a0a9-6225e6913da0
-- title:
--   Original source Lévy small-jump nonlinear test-function energy is finite on every compact smooth reserve band
-- statement:
--   Let X be the actual spectrally negative Lévy source with its original ν. On any compact interior reserve band [u,v] strictly inside a C¹ region of the verification function w, each negative mark z in (-δ,0) maps the reserve x back into that band provided u+δ≤x≤v. The nonlinear jump test-function amplitude then has a uniform Lipschitz bound M|z|, obtained by the convex mean-value theorem from a compact bound for w'. Consequently its squared amplitude has finite original-ν integral, by the Lévy-square integrability condition ∫ min(1,z²)ν(dz)<∞. This is the exact local quadratic-energy requirement for the source small-jump martingale and does not require or assume ∫|z|ν<∞. No source jump-count martingale, Brownian part, finite-variation Itô formula, or corrected full verification bound is claimed.
-- source:
--   Avram–Palmowski–Pistorius 2007 Proposition 4(i) unbounded-variation C² verification. Formal source lemma uses canonical derivative_abs_le_on_compact_interior_interval UUID 98c2c058-e613-4558-8ab5-aa80e20cbf55 and actual X.ν_integrable, the pin-confirmed convex mean-value and set-lintegral estimates. Complete 78-line source passed pinned private remote elaboration to intentional sentinel job c771fce3-cc97-49c9-8b3d-60e78cdcdc7b with no candidate errors. It supplies local source-X small-jump quadratic energy for corrected primary UUID 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04_source_small_negative_local_test_increment_energy_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (x δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hxu : u + δ ≤ x) (hxv : x ≤ v) :
    (∫⁻ z in Ioo (-δ) (0 : ℝ),
      ENNReal.ofReal ((w (x + z) - w x) ^ 2) ∂X.ν) < ⊤ := by sorry
