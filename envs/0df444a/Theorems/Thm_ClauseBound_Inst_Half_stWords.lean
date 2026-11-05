-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_stWords
-- name    : ClauseBound.Inst.Half.stWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:42:34.657126+00:00
-- url     : https://prove2.me/theorems/453d4219-8279-4796-82c8-f4ede1a491f0
-- title:
--   Half: st Words
-- statement:
--   A sum over all words of c bits of a product of two functions of the entry of a list with at most
--   2^c entries is the sum over the list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfLabs.lean#L152-L152
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfLabs.lean#L152-L152

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_ClauseBound_Inst_HalfLabs
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Part Partitions
open Labs

theorem ClauseBound.Inst.Half.stWords : StWords := by sorry
