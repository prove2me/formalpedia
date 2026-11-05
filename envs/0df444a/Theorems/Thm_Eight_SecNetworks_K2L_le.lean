-- Prove2me | Theorems.Thm_Eight_SecNetworks_K2L_le
-- name    : Eight.SecNetworks.K2L_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:24:13.129326+00:00
-- url     : https://prove2.me/theorems/cf36e3dc-b21d-487c-aa3e-abbd22c3f3ae
-- title:
--   Sec Networks: K2 L le
-- statement:
--   «K²L ≤ K² + U + gP/K» (end of the proof of Lemma 1), multiplied by K, for L = max{1, ⌊(U +
--   gP/K)/K²⌋}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_LemGrouping.lean#L260-L260
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_LemGrouping.lean#L260-L260

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

theorem Eight.SecNetworks.K2L_le (K g U P : ℕ) : K ^ 3 * Paper.groupedLength K g U P ≤ K ^ 3 + K * U + g * P := by sorry
