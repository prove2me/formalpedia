-- Prove2me | Theorems.Thm_AvramDividend_Classical_geometric_renewal_from_scaled_kernel_real_density
-- name    : AvramDividend.Classical.geometric_renewal_from_scaled_kernel_real_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:30:44.999575+00:00
-- url     : https://prove2.me/theorems/c63bbe93-efe9-4dbf-bdd9-eacc88008cd7
-- title:
--   Finite geometric renewal witness has exact normalised real convolution-series density
-- statement:
--   Start with an s-finite positive convolution kernel κ and its measure powers m_0=δ_0, m_(n+1)=κ∗m_n. If the Esscher-scaled kernel c•κ has a nonnegative real Lebesgue density k and F_n are its summable real convolution powers, then the entire weighted measure renewal sum c^(n+1)•m_n equals c times the initial Dirac atom plus Lebesgue measure with the real shifted density series. The initial positive power m_1 equals κ because convolution by δ_0 is the identity. The newly Proved scaled convolution-power density theorem establishes each positive-order measure identity, which the Proved geometric atom-plus-density theorem then sums. This gives the exact normalised stochastic-to-real renewal series bridge required by the bounded-variation Esscher route to cstar_lt_top.
-- source:
--   Canonical Proved geometric_scaled_convolution_powers_real_density and geometric_renewal_measure_atom_plus_real_density; pinned Mathlib Measure.conv_dirac_zero.

import Mathlib.MeasureTheory.Group.Convolution
import Theorems.Thm_AvramDividend_Classical_geometric_scaled_convolution_powers_real_density
import Theorems.Thm_AvramDividend_Classical_geometric_renewal_measure_atom_plus_real_density
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.geometric_renewal_from_scaled_kernel_real_density
    (c : ℝ≥0∞) (κ : Measure ℝ) [SFinite κ]
    (k : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (m : ℕ → Measure ℝ)
    (hkpos : ∀ x : ℝ, 0 ≤ k x)
    (hFpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hkmeas : Measurable k) (hFmeas : ∀ n : ℕ, Measurable (F n))
    (hconv : ∀ n : ℕ, ∀ x : ℝ,
      Integrable (fun y : ℝ => k y * F n (x - y)) volume)
    (hFsummable : ∀ x : ℝ,
      Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else F (n - 1) x))
    (hFzero : F 0 = k)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, k y * F n (x - y) ∂volume)
    (hκscaled : c • κ = volume.withDensity
      (fun x : ℝ => ENNReal.ofReal (k x)))
    (hmzero : m 0 = Measure.dirac (0 : ℝ))
    (hmsucc : ∀ n : ℕ, m (n + 1) = κ.conv (m n))
    (hmsfinite : ∀ n : ℕ, SFinite (m n)) :
    Measure.sum (fun n : ℕ => c ^ (n + 1) • m n) =
      c • (Measure.dirac (0 : ℝ) +
        volume.withDensity (fun x : ℝ =>
          ENNReal.ofReal (∑' n : ℕ,
            if n = 0 then (0 : ℝ) else F (n - 1) x))) := by sorry
