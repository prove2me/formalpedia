-- Prove2me | Theorems.Thm_AaronsonAmbainis_Dual_sum_mul_sum_mem
-- name    : AaronsonAmbainis.Dual.sum_mul_sum_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:41:33.663663+00:00
-- url     : https://prove2.me/theorems/650c38a3-f69a-44b3-991e-320f84be73aa
-- title:
--   Dual: sum mul sum mem
-- statement:
--   The Dual construction uses the sum mul sum mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Core.lean#L27-L39
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Core.lean#L27-L39

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Dual_Core
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Dual.sum_mul_sum_mem (κ : Finset ι → ℝ) (a : ι → ℝ) :
    ∑ S, κ S * ∑ i ∈ S, a i
      = ∑ i, a i * ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S := by sorry
