-- Prove2me | Theorems.Thm_Eight_SecNetworks_gated_runs
-- name    : Eight.SecNetworks.gated_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:28:19.613539+00:00
-- url     : https://prove2.me/theorems/790ea4c4-7ba7-4911-b3eb-150c436006cf
-- title:
--   Sec Networks: gated runs
-- statement:
--   If the test and the procedure each take at most τ steps on states of size at most S, then
--   `gated` takes at most 2τ + 1 steps on states of size at most S + 4 + the size of the input. The
--   procedure needs to work only where the test says yes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_LemGrouping.lean#L52-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_LemGrouping.lean#L52-L62

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
variable {α : Type} [HasSize α]

theorem Eight.SecNetworks.gated_runs {M : Stepped α Bool} {N : Stepped α ℤ} {a : α} {τ S : ℕ} {b : Bool} {v : ℤ} (hτ : 1 ≤ τ) (h : M.Runs a τ S b)
    (h' : b = true → N.Runs a τ S v) : (gated M N).Runs a (2 * τ + 1) (size a + S + 4) (if b = true then v else 0) := by sorry
