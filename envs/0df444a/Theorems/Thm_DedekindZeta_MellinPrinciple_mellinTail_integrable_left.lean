-- Prove2me | Theorems.Thm_DedekindZeta_MellinPrinciple_mellinTail_integrable_left
-- name    : DedekindZeta.MellinPrinciple.mellinTail_integrable_left
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:55:20.459881+00:00
-- url     : https://prove2.me/theorems/a4ce6d6f-4596-4a50-8146-c755cbf641b9
-- title:
--   Mellin Principle: mellin Tail integrable left
-- statement:
--   **Integrability of the `f`-summand of the tail on `Ioi 1`.** The integrand
--   is `O(y^{−2})` near `∞` (super-polynomial decay of `f y − a₀`).
--
--   -- the Mellin principle proof
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/MellinPrinciple.lean#L371-L374
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/MellinPrinciple.lean#L371-L374

import Mathlib
import Definitions.Def_DedekindZeta_MellinPrinciple
set_option autoImplicit true
open MeasureTheory Set Filter Asymptotics Topology Complex
open DedekindZeta DedekindZeta.MellinPrinciple
variable {f g : ℝ → ℂ} {a₀ b₀ C : ℂ} {k c α : ℝ}

theorem DedekindZeta.MellinPrinciple.mellinTail_integrable_left (h : IsMellinPair f g a₀ b₀ C k c α) {s : ℂ} :
    IntegrableOn (fun y : ℝ => (f y - a₀) * (y : ℂ) ^ (s - 1)) (Ioi (1 : ℝ)) := by sorry
