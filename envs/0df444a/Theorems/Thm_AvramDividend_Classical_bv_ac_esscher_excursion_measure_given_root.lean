-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_excursion_measure_given_root
-- name    : AvramDividend.Classical.bv_ac_esscher_excursion_measure_given_root
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T07:15:07.742266+00:00
-- url     : https://prove2.me/theorems/e56a853a-bdeb-46b0-b91f-74aa84cbef18
-- title:
--   Atomless excursion-height measure and zero-scale identity for a BV Esscher root
-- statement:
--   Given a standing bounded-variation spectrally negative Lévy process with absolutely continuous jump law and a fixed positive Cramér root, construct a positive-height excursion-intensity measure with finite positive tails, no singleton atoms, and its zero-discount scale-function integral representation. Continuity of the tail is a consequence of the existing Proved continuousOn_measureReal_Ici_of_finite_pos_noAtoms and is intentionally omitted here. The root itself and the analytic Esscher change-of-measure consequences are treated in separate proved/project lemmas.
-- source:
--   Chan, Kyprianou and Savov (2011), equations (3)-(6); Kuznetsov, Kyprianou and Rivero (2012), Lemma 2.4 and section 2.4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.bv_ac_esscher_excursion_measure_given_root
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
      (∀ x : ℝ, 0 < x → W x = Real.exp (φ * x) * V x) ∧
      (∀ a b : ℝ, 0 < a → a ≤ b →
        V b = V a * Real.exp (∫ t in a..b, μ.real (Ici t))) := by sorry
