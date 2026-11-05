-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_RunF_runF_eq
-- name    : ClauseBound.ParityChecks.RunF.runF_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:36:01.677728+00:00
-- url     : https://prove2.me/theorems/538a8ee4-6c2b-4f84-ad8b-4c10cafe34dc
-- title:
--   Run F: run F eq
-- statement:
--   The choice of the checks in the program is the run.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/RunF.lean#L131-L133
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/RunF.lean#L131-L133

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_ParityChecks_RunF
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.RunF
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.ParityChecks.Run
variable (pad : U) (q : Par) (oA : List Chk → ℤ) (oB : List Chk → Chk → ℕ → ℕ → ℤ)
variable {pad q oA oB}
variable {Idx : Type} [Enc Idx] (S : Solver Idx) (k : ℕ) (pad : U) (i : Idx) (n Δ : ℕ) (q : Par) (ψ : Fml)

theorem ClauseBound.ParityChecks.RunF.runF_eq (hF : 8 * (6 * n + 1) * (Δ * n + 1) * (Nat.size (Δ * n) + 2) + 8 ≤ pad.length) (hr : q.r ≤ 6 * n) (hm : q.m ≤ Δ * n) :
    runF S k pad i n Δ q ψ = q.run (orcA S k pad i n Δ q ψ) (orcB S k pad i n Δ q ψ) := by sorry
