-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_esscher_untilting_second_deriv
-- name    : AvramDividend.Classical.avram_wave3_05_esscher_untilting_second_deriv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:20:27.93621+00:00
-- url     : https://prove2.me/theorems/f7c34d8d-b85a-41b8-8692-6dfaa4bfe6fc
-- title:
--   Exact Gaussian Esscher untilting second derivative with signed Neumann density
-- statement:
--   For the genuine Gaussian tilted q-scale V=e^(-φx)W, the source Volterra theorem gives V'=g and signed Gaussian Neumann analysis gives g'=e^(wx)S/a, where S is a global L1 signed density. Undoing the exponential tilt yields W''=2φW'−φ²W+e^((φ+w)x)S/a on every positive reserve. This is the exact algebraic formula required to convert the known weighted W,W' and signed Neumann L1 estimates into a weighted W'' estimate.
-- source:
--   Gaussian original Lévy Esscher renewal identity, pinned Mathlib HasDerivAt and differentiability of the exponential; no generator harmonicity assumed.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Ring

open Set

theorem AvramDividend.Classical.avram_wave3_05_esscher_untilting_second_deriv
    (V g S : ℝ → ℝ) (φ w a : ℝ)
    (hV : ∀ x : ℝ, 0 < x → HasDerivAt V (g x) x)
    (hg : ∀ x : ℝ, 0 < x →
      HasDerivAt g (Real.exp (w * x) * (S x / a)) x) :
    ∀ x : ℝ, 0 < x →
      let W : ℝ → ℝ := fun z => Real.exp (φ * z) * V z
      deriv (deriv W) x =
        2 * φ * deriv W x - φ ^ 2 * W x +
          Real.exp ((φ + w) * x) * (S x / a) := by sorry
