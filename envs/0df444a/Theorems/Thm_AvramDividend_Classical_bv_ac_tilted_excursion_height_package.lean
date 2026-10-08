-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_ac_tilted_excursion_height_package
-- name    : AvramDividend.Classical.bv_ac_tilted_excursion_height_package
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T06:49:47.748829+00:00
-- url     : https://prove2.me/theorems/a94ff49d-abec-4cd6-a78e-c3d19169619e
-- title:
--   Bounded-variation Esscher change of measure and atomless excursion-height representation
-- statement:
--   For a standing bounded-variation process with absolutely continuous Levy measure, build the positive Esscher exponent, tilted zero-discount scale function V, and excursion-height intensity measure mu. The measure is atomless with finite positive tails and a continuous positive-axis tail. The Esscher relation links W and V, while the zero-discount excursion identity gives V(b)=V(a)exp(integral mu([t,infinity))). This is the stochastic probabilistic core; the separate published analytic Esscher transfer lemma derives the q-scale interval identity.
-- source:
--   Chan, Kyprianou and Savov (2011), Smoothness of scale functions for spectrally negative Levy processes, equations (3)-(6), plus Kuznetsov, Kyprianou and Rivero (2012), equations (2.17)-(2.19).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.bv_ac_tilted_excursion_height_package
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hac : X.ν ≪ volume) :
    ∃ (φ : ℝ) (V : ℝ → ℝ) (μ : Measure ℝ),
      0 < φ ∧ NullSingletonClass μ ∧
      (∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) ∧
      ContinuousOn (fun t : ℝ => μ.real (Ici t)) (Ioi 0) ∧
      (∀ x : ℝ, 0 < x → W x = Real.exp (φ * x) * V x) ∧
      (∀ a b : ℝ, 0 < a → a ≤ b →
        V b = V a * Real.exp (∫ t in a..b, μ.real (Ici t))) := by sorry
