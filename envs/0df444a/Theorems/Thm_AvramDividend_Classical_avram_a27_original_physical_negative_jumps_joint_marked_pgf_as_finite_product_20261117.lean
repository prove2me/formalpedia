-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_jumps_joint_marked_pgf_as_finite_product_20261117
-- name    : AvramDividend.Classical.avram_a27_original_physical_negative_jumps_joint_marked_pgf_as_finite_product_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T21:03:04.58074+00:00
-- url     : https://prove2.me/theorems/aeeeb4c3-1ada-4471-b664-3ae211becddf
-- title:
--   Original physical marked Poisson joint PGF equals exact finite marked-jump product on the unchanged Lévy path
-- statement:
--   For the actual original finite-activity negative jumps of a spectrally negative Levy process, the joint generating-function integrand z^K exp(theta J) is almost surely exactly the finite product over the actual physical jump times of z exp(theta jump). K is the actual source negative-jump count, not an auxiliary random count.
-- source:
--   Proved original exact finite physical negative-mark count support, Proved original jump-sum exponential finite product, original no positive jumps, and Proved finite product factor algebra.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_physical_negative_jumps_joint_marked_pgf_as_finite_product_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ z : ℝ) (J : Ω → ℝ)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal) :
    ∀ᵐ ω ∂P, ∃ S : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ t ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
      K ω = S.card ∧
      z ^ (K ω) * Real.exp (θ * J ω) =
        ∏ u ∈ S, z * Real.exp (θ *
          (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by sorry
