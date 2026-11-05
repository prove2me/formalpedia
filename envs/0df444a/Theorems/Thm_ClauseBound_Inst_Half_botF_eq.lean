-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_botF_eq
-- name    : ClauseBound.Inst.Half.botF_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:41:01.673634+00:00
-- url     : https://prove2.me/theorems/281d03e4-0ec7-4a72-ae72-7453ecc9d175
-- title:
--   Half: bot F eq
-- statement:
--   `botF` computes the entries of (h!/z_μ)·μ[r].
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabBot.lean#L37-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabBot.lean#L37-L49

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Inst_HalfTabBot
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson

theorem ClauseBound.Inst.Half.botF_eq {pad : U} {W : ℕ} {flat : List (List ℕ)} {μ : List ℕ} (hW : 1 ≤ W) (hf : FlatOK W flat) (hμ : ∀ n ∈ μ, n ≤ W)
    (hp : padOp W flat.length μ.length ≤ pad.length) (h : ℕ) (r : ℤ) {π σ : List ℕ} (hπ : π ∈ flat) (hσ : σ ∈ flat) :
    botF pad W flat h μ r π σ = ClauseBound.Boson.botK μ h r ↑π ↑σ := by sorry
