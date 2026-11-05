-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Count_toNat_eq
-- name    : ClauseBound.ParityChecks.Count.toNat_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:36:37.371573+00:00
-- url     : https://prove2.me/theorems/c285cdb5-39ca-4567-ae58-739568caf9f9
-- title:
--   Count: to Nat eq
-- statement:
--   If a ≡ 2^r·N modulo 2^(β−1+r+1), β ≥ n + 2 and 0 ≤ N ≤ 2^n, then N is the remainder of a/2^r
--   modulo 2^(n+1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Count.lean#L113-L118
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Count.lean#L113-L118

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_ClauseBound_ParityChecks_RunF
import Definitions.Def_PaddedDescent_F_Eval
import Definitions.Def_PaddedDescent_F_Eval
import Definitions.Def_ClauseBound_ParityChecks_Count
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Count
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Eval ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW _root_.ParityChecks

theorem ClauseBound.ParityChecks.Count.toNat_eq {a : ℤ} {N n r β : ℕ} (h : a ≡ 2 ^ r * (N : ℤ) [ZMOD 2 ^ (β - 1 + r + 1)]) (hβ : n + 2 ≤ β) (hN : N ≤ 2 ^ n) :
    ((a / 2 ^ r) % 2 ^ (n + 1)).toNat = N := by sorry
