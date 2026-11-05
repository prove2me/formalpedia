-- Prove2me | Theorems.Thm_Eight_SecNetworks_L_le
-- name    : Eight.SecNetworks.L_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:18:31.43078+00:00
-- url     : https://prove2.me/theorems/76a8c31c-7f40-47e1-821e-f75906272293
-- title:
--   Sec Networks: L le
-- statement:
--   «L ≤ 2gP» (end of the proof of Lemma 1), for L = max{1, ⌊(U + gP/K)/K²⌋} and U ≤ gP.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_LemGrouping.lean#L263-L273
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_LemGrouping.lean#L263-L273

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

theorem Eight.SecNetworks.L_le {K g U P : ℕ} (hK : 1 ≤ K) (hg : 1 ≤ g) (hP : 1 ≤ P) (hU : U ≤ g * P) : Paper.groupedLength K g U P ≤ 2 * (g * P) := by sorry
