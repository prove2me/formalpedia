-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_partT_eq
-- name    : ClauseBound.Inst.Half.partT_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:40:26.127757+00:00
-- url     : https://prove2.me/theorems/917e4f75-f25b-4f14-8475-a6f4abc8a681
-- title:
--   Half: part T eq
-- statement:
--   What `partT` returns on the table of all partitions of 0, …, 4h, if the pad is long enough and
--   the partitions of the two strings are listed and have weight h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfVal.lean#L78-L93
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfVal.lean#L78-L93

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfVal
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec Finset
open Val

theorem ClauseBound.Inst.Half.partT_eq (hT : StTopF) (hB : StBotF) {h : ℕ} (hh : 1 ≤ h) {pad : U} (hp : padLen h ≤ pad.length) (tr top : Bool) (s : ℤ) (a b θ : List Bool)
    (ha : encF (allTab (4 * h)) h a ∈ (allTab (4 * h)).flatten ∧ (encF (allTab (4 * h)) h a).sum = h)
    (hb : encF (allTab (4 * h)) h b ∈ (allTab (4 * h)).flatten ∧ (encF (allTab (4 * h)) h b).sum = h) :
    partT pad tr top h s (allTab (4 * h)) a b θ =
      ((labs (allTab (4 * h)) tr h s)[ofWord θ]?).elim 0 (valK tr top h s (encF (allTab (4 * h)) h a) (encF (allTab (4 * h)) h b)) := by sorry
