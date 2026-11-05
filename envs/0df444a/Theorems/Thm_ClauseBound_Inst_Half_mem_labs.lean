-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_mem_labs
-- name    : ClauseBound.Inst.Half.mem_labs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:40:10.003234+00:00
-- url     : https://prove2.me/theorems/d14fa8d3-cdfc-470e-b020-9a4639d8370c
-- title:
--   Half: mem labs
-- statement:
--   What it means to be in the list of the pairs (j, τ).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfLabs.lean#L97-L111
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfLabs.lean#L97-L111

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

theorem ClauseBound.Inst.Half.mem_labs {T : PT} {tr : Bool} {h : ℕ} {s : ℤ} {p : ℕ × List ℕ} :
    p ∈ labs T tr h s ↔ p.1 ≤ 2 * h ∧ 0 ≤ wOf tr h s p.1 ∧ p.2 ∈ T.getD (wOf tr h s p.1).toNat [] := by sorry
