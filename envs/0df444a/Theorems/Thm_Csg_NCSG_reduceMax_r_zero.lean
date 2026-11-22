-- Prove2me | Theorems.Thm_Csg_NCSG_reduceMax_r_zero
-- name    : Csg.NCSG.reduceMax_r_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:43:28.00774+00:00
-- url     : https://prove2.me/theorems/5a111795-1db1-42a5-bfdb-71e1a5804e08
-- title:
--   NCSG: reduce Max r zero
-- statement:
--   The `reduceMax` counterpart of `reduceMin_r_zero`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CoalitionComplement.lean#L114-L115
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CoalitionComplement.lean#L114-L115

import Definitions.Def_Csg_Coalition
import Definitions.Def_Csg_CoalitionComplement
set_option autoImplicit true
open Csg
open Csg.NCSG
variable {S Players : Type*} {A : Players → Type*}
  [Fintype S] [Fintype Players] [DecidableEq Players]
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
variable (C : Finset Players)
variable (G : NCSG S Players A)

theorem Csg.NCSG.reduceMax_r_zero (hrG : ∀ s a, G.r s a = 0) :
    ∀ s a1 a2, (G.reduceMax C).r s a1 a2 = 0 := by sorry
