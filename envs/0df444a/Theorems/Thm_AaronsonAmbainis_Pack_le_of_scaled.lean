-- Prove2me | Theorems.Thm_AaronsonAmbainis_Pack_le_of_scaled
-- name    : AaronsonAmbainis.Pack.le_of_scaled
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:42:01.008365+00:00
-- url     : https://prove2.me/theorems/51acc790-671b-49c7-84a6-7d2f7551e5a9
-- title:
--   Pack: le of scaled
-- statement:
--   The limit step: if `M² L ≤ d² (π M + 2)² + C` for every natural `M ≥ 1`, then
--   `L ≤ π² d²`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Pack/Packing.lean#L16-L63
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Pack/Packing.lean#L16-L63

import Definitions.Def_AaronsonAmbainis_Pack_Scaled
import Definitions.Def_AaronsonAmbainis_Pack_Packing
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Pack

theorem AaronsonAmbainis.Pack.le_of_scaled (L C : ℝ) (d : ℕ)
    (key : ∀ M : ℕ, 0 < M → (M : ℝ) ^ 2 * L ≤ (d : ℝ) ^ 2 * (Real.pi * (M : ℝ) + 2) ^ 2 + C) :
    L ≤ Real.pi ^ 2 * (d : ℝ) ^ 2 := by sorry
