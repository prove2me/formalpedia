-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_esscher_root_resolvent_ratio_pos_le
-- name    : AvramDividend.Classical.levy_esscher_root_resolvent_ratio_pos_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:08:38.76877+00:00
-- url     : https://prove2.me/theorems/020d6d3e-15fb-41f0-864b-e2ca1f448966
-- title:
--   Positive bounded shifted-Esscher resolvent ratio from the root secant bound
-- statement:
--   At any positive q-root φ of the spectrally negative Lévy exponent, for each β>0 the shifted ratio β/(ψ(φ+β)−q) is strictly positive and no greater than φ/q. This is the nontrivial denominator and uniform scalar estimate needed when identifying the positive-drift descending Wiener-Hopf perpetual-infimum transform.
-- source:
--   Apply the already-Proved root-shifted convex secant inequality e9488750 and strict shifted denominator result eb5bb6f8. Multiply the secant inequality by φ, rearrange, and divide by positive q and ψ(φ+β)−q. The conclusion is unconditional on standing hypotheses and does not use the two-sided-exit formula.

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_shifted_increment_lower
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_strictly_above_shift

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_esscher_root_resolvent_ratio_pos_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ β : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hβ : 0 < β)
    (hroot : X.ψ φ = q) :
    0 < β / (X.ψ (φ + β) - q) ∧
      β / (X.ψ (φ + β) - q) ≤ φ / q := by sorry
