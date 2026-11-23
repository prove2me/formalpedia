-- Prove2me | Theorems.Thm_DedekindZeta_MellinPrinciple_reducedMellin_lower
-- name    : DedekindZeta.MellinPrinciple.reducedMellin_lower
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:22:04.552408+00:00
-- url     : https://prove2.me/theorems/57c9c543-a0cf-4aec-a063-4dff326dbfa7
-- title:
--   Mellin Principle: reduced Mellin lower
-- statement:
--   **The lower-range integral via the inversion law.** Substituting `y ↦ 1/y`
--   in `∫_{Ioc 0 1} (f y − a₀) y^{s−1} dy` and applying `f(1/y) = C y^k g(y)`
--   produces the constant-term boundary integral `−a₀/s`, the pole term
--   `C b₀/(s−k)`, and the `g`-part of the tail.
--
--   -- the Mellin principle proof
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/MellinPrinciple.lean#L400-L513
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/MellinPrinciple.lean#L400-L513

import Mathlib
import Definitions.Def_DedekindZeta_MellinPrinciple
set_option autoImplicit true
open MeasureTheory Set Filter Asymptotics Topology Complex
open DedekindZeta DedekindZeta.MellinPrinciple
variable {f g : ℝ → ℂ} {a₀ b₀ C : ℂ} {k c α : ℝ}

theorem DedekindZeta.MellinPrinciple.reducedMellin_lower (h : IsMellinPair f g a₀ b₀ C k c α) {s : ℂ}
    (hs : k < s.re) :
    (∫ y in Ioc (0 : ℝ) 1, (f y - a₀) * (y : ℂ) ^ (s - 1))
      = -a₀ / s + C * b₀ / (s - (k : ℂ))
        + ∫ y in Ioi (1 : ℝ), C * (g y - b₀) * (y : ℂ) ^ ((k : ℂ) - s - 1) := by sorry
