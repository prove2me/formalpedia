-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_sum_words_getElem
-- name    : ClauseBound.Inst.Half.sum_words_getElem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:39:54.988428+00:00
-- url     : https://prove2.me/theorems/f52f11bb-c50f-4aa2-9984-47d70631d87d
-- title:
--   Half: sum words get Elem
-- statement:
--   A sum over all words θ of c bits of the product of two functions of the entry number θ of a list
--   with at most 2^c entries is the sum over the list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfLabs.lean#L51-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfLabs.lean#L51-L56

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_ClauseBound_Inst_HalfLabs
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Part Partitions
open Labs

theorem ClauseBound.Inst.Half.sum_words_getElem {β : Type} (L : List β) (c : ℕ) (hL : L.length ≤ 2 ^ c) (f g : β → ℤ) :
    ∑ θ ∈ words c, (L[ofWord θ]?).elim 0 f * (L[ofWord θ]?).elim 0 g = (L.map fun b => f b * g b).sum := by sorry
