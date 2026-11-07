-- Prove2me | Theorems.Thm_AaronsonAmbainis_sum_ite_ite_mem
-- name    : AaronsonAmbainis.sum_ite_ite_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:29:42.939432+00:00
-- url     : https://prove2.me/theorems/f2c64887-b4ae-41f8-96f3-cec2c1a14b61
-- title:
--   Aaronson Ambainis: sum ite ite mem
-- statement:
--   A sum of products of two restricted vectors is a sum over the restriction set.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/AllPairsCore.lean#L53-L64
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/AllPairsCore.lean#L53-L64

import Definitions.Def_AaronsonAmbainis_TwoSided_Glue
import Definitions.Def_AaronsonAmbainis_TwoSided_AllPairsCore
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.sum_ite_ite_mem (F : Finset ι) (w a b : ι → ℝ) :
    ∑ j, w j * (if j ∈ F then a j else 0) * (if j ∈ F then b j else 0)
      = ∑ j ∈ F, w j * a j * b j := by sorry
