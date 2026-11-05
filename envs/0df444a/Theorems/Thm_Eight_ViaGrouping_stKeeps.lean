-- Prove2me | Theorems.Thm_Eight_ViaGrouping_stKeeps
-- name    : Eight.ViaGrouping.stKeeps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:39:14.009646+00:00
-- url     : https://prove2.me/theorems/a78e068d-804d-46cf-ab0f-ad01c0d11bff
-- title:
--   Via Grouping: st Keeps
-- statement:
--   **The algorithm of the proof of Lemma 1 has polynomial-time steps** if the algorithm E for
--   cliques has: whenever the four procedures have polynomial-time steps and P_a, c_{a,b}, P are given
--   in unary, so has `netAlg K g E` on them.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Keeps.lean#L138-L147
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Keeps.lean#L138-L147

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_Eight_ViaGrouping_Keeps
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Stepped Eight.SecNetworks
variable {C : Type} [HasSize C] [Enc C] [Carried C] (K g : ℕ) {Np : Procs C}

theorem Eight.ViaGrouping.stKeeps : StKeeps := by sorry
