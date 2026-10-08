-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_excursion_identity_given_root
-- name    : AvramDividend.Classical.bv_ac_esscher_excursion_identity_given_root
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T07:09:37.06146+00:00
-- url     : https://prove2.me/theorems/7d6b82d7-8d66-4005-8d7c-5a2d72d90b43
-- title:
--   Atomless zero-discount excursion representation after a supplied Esscher root
-- statement:
--   Given the positive Cramér–Esscher root, construct the tilted zero-discount scale function V and the excursion-height intensity measure μ of the reflected tilted process. The Lévy-measure tilt preserves absolute continuity and bounded variation. Establish finite positive excursion-height tails, absence of atoms including at zero, continuity of the positive-axis tail, and the zero-discount integrated excursion formula. The derivative and deterministic exponential transfer are separate previously proved children.
-- source:
--   Chan, Kyprianou and Savov (2011), equations (3)-(6); Kuznetsov, Kyprianou and Rivero (2012), Lemma 2.4 and §2.4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.bv_ac_esscher_excursion_identity_given_root
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hac : X.ν ≪ volume)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ (V : ℝ → ℝ) (μ : Measure ℝ),
      NullSingletonClass μ ∧
      (∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) ∧
      ContinuousOn (fun t : ℝ => μ.real (Ici t)) (Ioi 0) ∧
      (∀ x : ℝ, 0 < x → W x = Real.exp (φ * x) * V x) ∧
      (∀ a b : ℝ, 0 < a → a ≤ b →
        V b = V a * Real.exp (∫ t in a..b, μ.real (Ici t))) := by sorry
