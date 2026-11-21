-- Prove2me | Theorems.Thm_Focil_noncompliant_block_not_canonical
-- name    : Focil.noncompliant_block_not_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:38:02.783109+00:00
-- url     : https://prove2.me/theorems/f54b303b-2711-482a-af8f-b3b30d9bcfb8
-- title:
--   Focil: noncompliant block not canonical
-- statement:
--   Direct contrapositive of `canonical_implies_compliant`: a block
--     that fails to be FOCIL-compliant against `fc`'s context cannot
--     be canonical under `fc`.
--
--     Useful as a builder-side incentive statement: "if I propose a
--     block that misses an obligation, my block is not canonical."
--
--   Source: https://github.com/rahulbarmann/focil-lean4/blob/d6832793e6c5153e58079252e4a29c29bf1b7138/Focil/ForkChoice.lean#L205-L211
-- source:
--   https://github.com/rahulbarmann/focil-lean4/blob/d6832793e6c5153e58079252e4a29c29bf1b7138/Focil/ForkChoice.lean#L205-L211

import Definitions.Def_Focil_Types
import Definitions.Def_Focil_Protocol
import Definitions.Def_Focil_ForkChoice
set_option autoImplicit false
open Focil

theorem Focil.noncompliant_block_not_canonical
    (fc : ForkChoice) (b : Block)
    (h_noncompliant : ¬ FocilCompliant fc.canAppend fc.full b fc.state) :
    ¬ IsCanonical fc b := by sorry
