-- Prove2me | Theorems.Thm_DedekindZeta_MellinPrinciple_reducedMellin_convergent
-- name    : DedekindZeta.MellinPrinciple.reducedMellin_convergent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:47:22.6231+00:00
-- url     : https://prove2.me/theorems/582ef04e-37cc-4471-b9a4-b4f34f1fd8c0
-- title:
--   Mellin Principle: reduced Mellin convergent
-- statement:
--   **Mellin principle, the Mellin principle (i), convergence.** For `Re s > k` the
--   reduced Mellin integral `L(f,s) = ∫_0^∞ (f y − a₀) y^s dy/y` converges
--   absolutely.
--
--   The proof combines the `s`-uniform majorant `B'/y²` near `∞`
--   (`reducedMellin_isBigO_atTop`) with the near-zero bound `O(y^{-k})`
--   (`reducedMellin_isBigO_zero`), feeding Mathlib's
--   `mellinConvergent_of_isBigO_rpow`.
--
--   -- the Mellin principle
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/MellinPrinciple.lean#L178-L183
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/MellinPrinciple.lean#L178-L183

import Mathlib
import Definitions.Def_DedekindZeta_MellinPrinciple
set_option autoImplicit true
open MeasureTheory Set Filter Asymptotics Topology Complex
open DedekindZeta DedekindZeta.MellinPrinciple
variable {f g : ℝ → ℂ} {a₀ b₀ C : ℂ} {k c α : ℝ}

theorem DedekindZeta.MellinPrinciple.reducedMellin_convergent (h : IsMellinPair f g a₀ b₀ C k c α) {s : ℂ}
    (hs : k < s.re) : MellinConvergent (fun y : ℝ => f y - a₀) s := by sorry
