-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_sum_map_labs
-- name    : ClauseBound.Inst.Half.sum_map_labs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:40:20.310056+00:00
-- url     : https://prove2.me/theorems/638c6c61-c6f3-46e1-9561-1439cad001d4
-- title:
--   Half: sum map labs
-- statement:
--   A sum over the list of the labels is the double sum of the expansion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfLabs.lean#L134-L146
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfLabs.lean#L134-L146

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_ClauseBound_Inst_HalfLabs
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Part Partitions
open Labs

theorem ClauseBound.Inst.Half.sum_map_labs {h : ℕ} {s : ℤ} (hs : |s| ≤ 2 * h) (tr : Bool) (G : ℕ → Multiset ℕ → ℤ) :
    ((labs (allTab (4 * h)) tr h s).map fun p => G p.1 (p.2 : Multiset ℕ)).sum
      = ∑ j ∈ range (2 * h + 1), ∑ τ ∈ ClauseBound.Boson.Pz (wOf tr h s j), G j τ := by sorry
