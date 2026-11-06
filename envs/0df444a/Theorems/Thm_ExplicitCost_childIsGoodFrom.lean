-- Prove2me | Theorems.Thm_ExplicitCost_childIsGoodFrom
-- name    : ExplicitCost.childIsGoodFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:41:31.008302+00:00
-- url     : https://prove2.me/theorems/5ad35b5a-6e8d-445c-8e94-0ff218611c61
-- title:
--   Explicit Cost: child Is Good From
-- statement:
--   **A call is good**, from Lemma 8 up to the call, its L, the bound on the entries, the fact that
--   the value of the clique is that of the network, and the printed steps on the network with the
--   smaller total.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ChildIsGood.lean#L46-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ChildIsGood.lean#L46-L78

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CallFacts
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ChildIsGood
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.childIsGoodFrom : ChildIsGoodFrom := by sorry
