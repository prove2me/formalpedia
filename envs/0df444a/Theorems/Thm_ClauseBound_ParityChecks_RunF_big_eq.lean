-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_RunF_big_eq
-- name    : ClauseBound.ParityChecks.RunF.big_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:48:15.439594+00:00
-- url     : https://prove2.me/theorems/5640a938-b09f-4936-a434-7392ddfcdeaa
-- title:
--   Run F: big eq
-- statement:
--   The length that the program asks of the pad, written as a product.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/RunF.lean#L112-L113
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/RunF.lean#L112-L113

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_ParityChecks_RunF
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.RunF
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.ParityChecks.Run
variable (pad : U) (q : Par) (oA : List Chk → ℤ) (oB : List Chk → Chk → ℕ → ℕ → ℤ)
variable {pad q oA oB}

theorem ClauseBound.ParityChecks.RunF.big_eq (n Δ : ℕ) : 8 * (6 * n + 1) * (Δ * n + 1) * (Nat.size (Δ * n) + 2) = 6 * n * (8 * ((Δ * n + 1) * (Nat.size (Δ * n) + 2))) + 8 * ((Δ * n + 1) * (Nat.size (Δ * n) + 2)) := by sorry
