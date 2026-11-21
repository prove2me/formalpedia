-- Prove2me | Theorems.Thm_Focil_canonical_implies_compliant
-- name    : Focil.canonical_implies_compliant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:38:00.36663+00:00
-- url     : https://prove2.me/theorems/565800a1-e2d4-4157-9acc-348db3f49e63
-- title:
--   Focil: canonical implies compliant
-- statement:
--   **Cornerstone lemma.** A canonical block under `fc` is
--     FOCIL-compliant against `fc.state` under `fc.full`.
--
--     Argument:
--
--     1. Canonicality unfolds to `HasQuorum b`.
--     2. By `quorum_has_honest_voter`, there exists an honest
--        validator `v` who voted for `b`.
--     3. By `honest_attester_compliance`, that vote forces FOCIL
--        compliance against `fc.state`.
--
--     This is the load-bearing step the safety theorem rests on.
--
--   Source: https://github.com/rahulbarmann/focil-lean4/blob/d6832793e6c5153e58079252e4a29c29bf1b7138/Focil/ForkChoice.lean#L188-L195
-- source:
--   https://github.com/rahulbarmann/focil-lean4/blob/d6832793e6c5153e58079252e4a29c29bf1b7138/Focil/ForkChoice.lean#L188-L195

import Definitions.Def_Focil_Types
import Definitions.Def_Focil_Protocol
import Definitions.Def_Focil_ForkChoice
set_option autoImplicit false
open Focil

theorem Focil.canonical_implies_compliant
    (fc : ForkChoice) (b : Block)
    (h_canon : IsCanonical fc b) :
    FocilCompliant fc.canAppend fc.full b fc.state := by sorry
