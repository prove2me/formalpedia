-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_positive_esscher_root
-- name    : AvramDividend.Classical.bv_positive_esscher_root
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:09:56.295285+00:00
-- url     : https://prove2.me/theorems/3f64cde9-90a3-4f08-a5f1-4eee88b89407
-- title:
--   Positive Esscher root in the standing bounded-variation Lévy branch
-- statement:
--   Under Standing and BoundedVariation, positive drift and the BV Lévy–Khintchine formula imply ψ(θ) exceeds q at some θ>0. Combine this growth with the existing proved canonical continuity of ψ on [0,∞), ψ(0)=0, and the existing proved positive_continuous_root_from_growth to obtain a positive Esscher root. Retain exact normalization of ψ and compensate the Lévy jump integral correctly.
-- source:
--   Spectrally negative Lévy Laplace exponent growth and IVT; Chan, Kyprianou and Savov (2011), positive Esscher root in equations (3)-(4).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.bv_positive_esscher_root
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hbv : X.BoundedVariation) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q := by sorry
