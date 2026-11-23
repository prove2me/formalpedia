-- Prove2me | Theorems.Thm_DedekindZeta_MellinPrinciple_mellinTail_integrable_right
-- name    : DedekindZeta.MellinPrinciple.mellinTail_integrable_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:47:03.548423+00:00
-- url     : https://prove2.me/theorems/ffc4d0be-ed3d-444c-bfea-7e92d6220aac
-- title:
--   Mellin Principle: mellin Tail integrable right
-- statement:
--   **Integrability of the `g`-summand of the tail on `Ioi 1`.** The integrand
--   is `O(y^{−2})` near `∞` (super-polynomial decay of `g y − b₀`).
--
--   -- the Mellin principle proof
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/MellinPrinciple.lean#L380-L392
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/MellinPrinciple.lean#L380-L392

import Mathlib
import Definitions.Def_DedekindZeta_MellinPrinciple
set_option autoImplicit true
open MeasureTheory Set Filter Asymptotics Topology Complex
open DedekindZeta DedekindZeta.MellinPrinciple
variable {f g : ℝ → ℂ} {a₀ b₀ C : ℂ} {k c α : ℝ}

theorem DedekindZeta.MellinPrinciple.mellinTail_integrable_right (h : IsMellinPair f g a₀ b₀ C k c α) {s : ℂ} :
    IntegrableOn
      (fun y : ℝ => C * (g y - b₀) * (y : ℂ) ^ ((k : ℂ) - s - 1)) (Ioi (1 : ℝ)) := by sorry
