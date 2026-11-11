-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger60_gaussian_scalar_HJB_one_sided_exponential_bound
-- name    : AvramDividend.Classical.avram_gledger60_gaussian_scalar_HJB_one_sided_exponential_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:22:52.893243+00:00
-- url     : https://prove2.me/theorems/cbc4fe95-a941-48f5-968a-1fecc9867268
-- title:
--   Gaussian HJB second-order supersolutions have a one-sided exponential spatial envelope
-- statement:
--   The HJB upper differential inequality for a positive diffusion coefficient and positive discount forces an exponential upper envelope on every positive spatial half-line. The proof assembles characteristic roots, weighted first-derivative comparison and the scalar exponential envelope, preserving the possibility of arbitrarily negative values of w. This is the exact deterministic growth condition for original Gaussian physical-source positive-part integrability.
-- source:
--   Root-connected original Gaussian source integrability gledger53: assemble Proved gledger56 characteristic roots, gledger58 scalar weighted ODE, and gledger57 one-sided exponential envelope before tackling original stopping-clock and discount source control.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger56_discounted_gaussian_characteristic_roots
import Theorems.Thm_AvramDividend_Classical_avram_gledger57_weighted_first_derivative_one_sided_exponential_envelope
import Theorems.Thm_AvramDividend_Classical_avram_gledger58_factorised_second_order_ode_weighted_first_derivative
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gledger60_gaussian_scalar_HJB_one_sided_exponential_bound
    (a b q u : ℝ) (ha : 0 < a) (hq : 0 < q) (hu : 0 < u)
    (w : ℝ → ℝ)
    (hsmooth : ∀ y : ℝ, 0 < y →
      HasDerivAt w (deriv w y) y ∧
        HasDerivAt (deriv w) (iteratedDeriv 2 w y) y)
    (hode : ∀ y : ℝ, 0 < y →
      a * iteratedDeriv 2 w y + b * deriv w y - q * w y ≤ 0) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, u ≤ y → w y ≤ K * Real.exp (θ * y) := by sorry
