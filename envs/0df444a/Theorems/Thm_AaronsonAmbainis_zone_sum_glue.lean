-- Prove2me | Theorems.Thm_AaronsonAmbainis_zone_sum_glue
-- name    : AaronsonAmbainis.zone_sum_glue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:29:43.999585+00:00
-- url     : https://prove2.me/theorems/99b2d782-1ab7-4823-be3a-d6dd06597253
-- title:
--   Aaronson Ambainis: zone sum glue
-- statement:
--   The left side of the antipodal inequality for the restricted function, in terms of
--   `allPairsTerm`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/AllPairsCore.lean#L68-L78
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/AllPairsCore.lean#L68-L78

import Definitions.Def_AaronsonAmbainis_TwoSided_Glue
import Definitions.Def_AaronsonAmbainis_TwoSided_AllPairsCore
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.zone_sum_glue (g : Cube ι → Bool) (w : ι → ℝ) (lam : Cube ι → ι → ℝ)
    (F : Finset ι) (z : Cube ι) :
    ∑ u ∈ zone (fun u => g (glue F z u)),
        (∑ j, w j * (if j ∈ F then lam (glue F z u) j else 0)
          * (if j ∈ F then lam (glue F z (antipode u)) j else 0))⁻¹
      = ∑ u, allPairsTerm g w lam F (glue F z u) := by sorry
