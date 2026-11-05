-- Prove2me | Theorems.Thm_Eight_SecNetworks_presents_toPaperNetwork
-- name    : Eight.SecNetworks.presents_toPaperNetwork
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:24:02.641938+00:00
-- url     : https://prove2.me/theorems/7b93797d-2348-46d3-bdd8-24e8ce7a531a
-- title:
--   Sec Networks: presents to Paper Network
-- statement:
--   If the four procedures give N within τ steps on states of size at most S (Definition 2(iii)),
--   then the procedures of proof/networks/Paper give `N.toPaperNetwork` within 2τ + 1 steps on states of
--   size at most S + (size of c) + 2·(size of g) + 4P + 6.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_LemGrouping.lean#L198-L239
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_LemGrouping.lean#L198-L239

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_SingleBitPieces_SecNetworks_LemGrouping
import Definitions.Def_ToTuring_Poly_Comb
import Mathlib.Tactic
import Definitions.Def_Eight_SecNetworks_LemGrouping
set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Groundwork Groundwork.Prog Finset Stepped

theorem Eight.SecNetworks.presents_toPaperNetwork {C : Type} [HasSize C] {Np : Procs C} {c : C} {g : ℕ} {N : Net g} {P B τ S : ℕ} (h : IsNetwork Np c N P B τ S) :
    Np.toPaperNetwork.Presents c N.toPaperNetwork (2 * τ + 1) (S + (size c + 2 * size g + 4 * P + 6)) := by sorry
