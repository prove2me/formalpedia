-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridPresents_bitsOf_bitsOf
-- name    : ClauseBound.Alg.GridPresents.bitsOf_bitsOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:13:41.877474+00:00
-- url     : https://prove2.me/theorems/32399ca5-47a1-46ab-b049-95b9e69ec51b
-- title:
--   Grid Presents: bits Of bits Of
-- statement:
--   A word of n bits, read as a function and written again, is the word.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L38-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L38-L43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_GridNet
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_ClauseBound_Alg_GridPresents
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridPresents
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg.GridNet

theorem ClauseBound.Alg.GridPresents.bitsOf_bitsOf {n : ℕ} {w : List Bool} (h : w.length = n) : ClauseBound.Alg.bitsOf (Groundwork.Grid.bitsOf n w) = w := by sorry
