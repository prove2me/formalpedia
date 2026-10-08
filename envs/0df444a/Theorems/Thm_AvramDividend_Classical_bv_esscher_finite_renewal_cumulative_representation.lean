-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_finite_renewal_cumulative_representation
-- name    : AvramDividend.Classical.bv_esscher_finite_renewal_cumulative_representation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T11:28:42.67269+00:00
-- url     : https://prove2.me/theorems/e4a07bef-413b-4cf7-84a6-3e8adf527200
-- title:
--   Finite positive geometric-renewal measure identifies the Esscher tilted BV scale function
-- statement:
--   For a standing spectrally negative BV Lévy process and any positive Esscher root φ satisfying ψφ=q>0, construct a finite positive measure β on ℝ whose right cumulative equals e^(-φ x)W^(q)(x) at every x>0. Unlike the already-Proved tilted BV cumulative-Laplace representation at an arbitrary shift φ=q/δ (which only yields local finiteness), the root shift gives total-mass finiteness because the discounted positive-jump kernel κ has mass α=∫z e^(-φz)ν_mag(dz)<δ, by the root identity and the elementary exponential inequality. Apply the geometric renewal convolution measure package, total-mass identity, and Laplace uniqueness. The positive finite limit follows automatically from the Proved positive_finite_measure_cumulative_converges, so this is a tightly isolated stochastic/renewal existence theorem.
-- source:
--   BV renewal equation, existing Proved positive geometric convolution/measure package, canonical Laplace transforms and the subcritical root kernel inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.bv_esscher_finite_renewal_cumulative_representation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ β : Measure ℝ,
      0 < β Set.univ ∧ β Set.univ ≠ ⊤ ∧
      (∀ x : ℝ, 0 < x →
        Real.exp (-(φ * x)) * W x = (β (Iic x)).toReal) := by sorry
