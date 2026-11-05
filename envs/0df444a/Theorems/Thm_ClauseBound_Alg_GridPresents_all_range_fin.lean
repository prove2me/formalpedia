-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridPresents_all_range_fin
-- name    : ClauseBound.Alg.GridPresents.all_range_fin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:13:33.869223+00:00
-- url     : https://prove2.me/theorems/b809e120-e5e7-4c03-9da2-ef88d7ffd98c
-- title:
--   Grid Presents: all range fin
-- statement:
--   A test on all i < n holds if and only if it holds for all i in Fin n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L27-L29
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L27-L29

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_GridNet
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_ClauseBound_Alg_GridPresents
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridPresents
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg.GridNet

theorem ClauseBound.Alg.GridPresents.all_range_fin (n : ℕ) (t : ℕ → Bool) : (List.range n).all t = true ↔ ∀ i : Fin n, t i = true := by sorry
