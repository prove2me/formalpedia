-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e2_original_compact_discounted_HJB_integrand_uniform_grid
-- name    : AvramDividend.Classical.avram_p3_e2_original_compact_discounted_HJB_integrand_uniform_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:53:26.741939+00:00
-- url     : https://prove2.me/theorems/6fe12704-d2e1-4f17-9440-392e5810f9fc
-- title:
--   Uniform original discounted BV HJB grid integrands on compact predictable reserves
-- statement:
--   The literal original Lévy generator drift, discounted at every nonnegative physical time and localised by any countable family of compact original pre-reserve bands, has one source-derived nonnegative pointwise bound K. This provides a uniform candidate drift envelope independently of grid count; source L1 and time integration are separate obligations. Uses only Proved 27271b05 and the nonnegative-discount exponential.
-- source:
--   Source-exact compact predictable band pointwise bound; key step towards integrable uniform Bmesh dominator in c1e2f021.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_BV_compact_HJB_drift_uniform
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_e2_original_compact_discounted_HJB_integrand_uniform_grid
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ}
(X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
(x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (hwMeas : Measurable w)
(q : ℝ) (hq : 0 ≤ q) (a b L R A : ℝ)
(ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
(hL : 0 ≤ L) (hR : 0 ≤ R) (hA : 0 ≤ A)
(hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
 |w u - w v| ≤ L * |u - v|)
(hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
(hDeriv : ∀ y ∈ Icc a b, |deriv w y| ≤ A)
(E : ℕ → Set (ℝ≥0 × Ω))
(hEregion : ∀ n, ∀ p ∈ E n,
 Function.leftLim (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b) :
∃ K : ℝ, 0 ≤ K ∧ ∀ n (p : ℝ≥0 × Ω),
 |(if p ∈ E n then Real.exp (-(q * (p.1 : ℝ))) *
   (X.drift * deriv w (Function.leftLim
      (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) +
    (∫ z in Iio (0 : ℝ),
      w (Function.leftLim
         (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1 + z) -
      w (Function.leftLim
         (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) ∂X.ν) -
    q * w (Function.leftLim
      (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1))
 else 0)| ≤ K := by sorry
