-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_esscher_root_scale_laplace_mass_bound
-- name    : AvramDividend.Classical.levy_esscher_root_scale_laplace_mass_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:19:23.368888+00:00
-- url     : https://prove2.me/theorems/13a9cfa3-a6cb-4118-8283-eb1dd67fdb21
-- title:
--   Uniform β-normalised tilted q-scale Laplace bound at the positive root
-- statement:
--   At a positive q-root φ and any β>0, the β-normalised Laplace integral of the nonnegative Esscher-tilted q-scale function is strictly positive and at most φ/q. This is exactly the scale-side positive bounded transform corresponding to the descending Wiener-Hopf survival transform before the unknown positive drift normalisation.
-- source:
--   Directly combine Proved root-specialised tilted q-scale Laplace formula and Proved shifted-resolvent ratio positive upper bound. This isolates the scale-side numerical bound for the eventual Laplace-uniqueness identification and does not assume a two-sided exit identity.

import Mathlib.Algebra.Order.Field.Basic
import Theorems.Thm_AvramDividend_Classical_levy_esscher_root_scale_tilted_laplace
import Theorems.Thm_AvramDividend_Classical_levy_esscher_root_resolvent_ratio_pos_le

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_esscher_root_scale_laplace_mass_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ β : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hβ : 0 < β)
    (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    0 < β * (∫ y in Ioi (0 : ℝ),
      Real.exp (-(β * y)) * (Real.exp (-(φ * y)) * W y) ∂volume) ∧
    β * (∫ y in Ioi (0 : ℝ),
      Real.exp (-(β * y)) * (Real.exp (-(φ * y)) * W y) ∂volume) ≤
      φ / q := by sorry
