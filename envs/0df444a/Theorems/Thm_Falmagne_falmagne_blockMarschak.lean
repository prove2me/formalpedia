-- Prove2me | Theorems.Thm_Falmagne_falmagne_blockMarschak
-- name    : Falmagne.falmagne_blockMarschak
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:26:48.249296+00:00
-- url     : https://prove2.me/theorems/89a51076-1de8-56ab-9487-23830fd32dc1
-- title:
--   Falmagne: falmagne block Marschak
-- statement:
--   Full Falmagne–Block–Marschak equivalence on an arbitrary finite alternative set.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Falmagne.lean#L74-L76
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Falmagne.lean#L74-L76

module
public import Definitions.Def_EconomicsNextProof_ChoiceMobius
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_PathChoice
public import Definitions.Def_EconomicsNextProof_Flow
public import Definitions.Def_EconomicsNextProof_Falmagne
set_option autoImplicit true
@[expose] public section
public section
open Falmagne
open EconomicsNextProof
variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

theorem Falmagne.falmagne_blockMarschak {p : Finset X → X → ℝ} (hp : IsChoiceRule p) :
    RandomUtilityRepresentable p ↔ BlockMarschakNonnegative p := by sorry
