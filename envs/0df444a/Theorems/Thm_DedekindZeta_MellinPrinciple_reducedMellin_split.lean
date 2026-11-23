-- Prove2me | Theorems.Thm_DedekindZeta_MellinPrinciple_reducedMellin_split
-- name    : DedekindZeta.MellinPrinciple.reducedMellin_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:22:14.225565+00:00
-- url     : https://prove2.me/theorems/34b4c8e2-8496-4086-b533-975f9097d74a
-- title:
--   Mellin Principle: reduced Mellin split
-- statement:
--   **Splitting the reduced Mellin integral at `y = 1`.** For `Re s > k` the
--   integrand `(f y − a₀) y^{s−1}` is integrable on `Ioi 0`, hence the integral over
--   `Ioi 0` is the sum of the integrals over `Ioc 0 1` and `Ioi 1`.
--
--   -- the Mellin principle proof
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/MellinPrinciple.lean#L344-L365
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/MellinPrinciple.lean#L344-L365

import Mathlib
import Definitions.Def_DedekindZeta_MellinPrinciple
set_option autoImplicit true
open MeasureTheory Set Filter Asymptotics Topology Complex
open DedekindZeta DedekindZeta.MellinPrinciple
variable {f g : ℝ → ℂ} {a₀ b₀ C : ℂ} {k c α : ℝ}

theorem DedekindZeta.MellinPrinciple.reducedMellin_split (h : IsMellinPair f g a₀ b₀ C k c α) {s : ℂ}
    (hs : k < s.re) :
    reducedMellin f a₀ s
      = (∫ y in Ioc (0 : ℝ) 1, (f y - a₀) * (y : ℂ) ^ (s - 1))
        + (∫ y in Ioi (1 : ℝ), (f y - a₀) * (y : ℂ) ^ (s - 1)) := by sorry
