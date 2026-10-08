-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_excursion_integrated_scale_representation
-- name    : AvramDividend.Classical.bv_ac_esscher_excursion_integrated_scale_representation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T23:42:46.625981+00:00
-- url     : https://prove2.me/theorems/29c8f02d-8f3d-4bd7-96bb-4c066677d35c
-- title:
--   Esscher excursion measure and integrated scale-function representation for the bounded-variation AC case
-- statement:
--   Construct the positive Esscher root and the tilted excursion-height intensity measure. Under bounded variation and absolute continuity of the Levy measure, jump-size atomlessness implies the tilted excursion-height intensity is atomless. Its positive tails are finite and continuous. The excursion no-crossing identity then yields the integrated exponential representation of the q-scale function for any positive endpoints a ≤ b. This is the probabilistic core; differentiating the interval identity is a separate analytic theorem.
-- source:
--   Chan, Kyprianou, Savov (2011), Smoothness of scale functions for spectrally negative Levy processes, equations (3)–(6); Kuznetsov, Kyprianou, Rivero (2012), The Theory of Scale Functions for Spectrally Negative Levy Processes, Lemma 2.4, formulas (2.17)–(2.19).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_ac_esscher_excursion_integrated_scale_representation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hac : X.ν ≪ volume) :
    ∃ (φ : ℝ) (μ : Measure ℝ),
      0 < φ ∧ NullSingletonClass μ ∧
      (∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) ∧
      ContinuousOn (fun t : ℝ => μ.real (Ici t)) (Ioi 0) ∧
      (∀ a b : ℝ, 0 < a → a ≤ b →
        W b = W a * Real.exp (∫ t in a..b, φ + μ.real (Ici t))) := by sorry
