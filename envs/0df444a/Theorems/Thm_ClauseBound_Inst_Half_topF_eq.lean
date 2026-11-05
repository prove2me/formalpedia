-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_topF_eq
-- name    : ClauseBound.Inst.Half.topF_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:40:51.962386+00:00
-- url     : https://prove2.me/theorems/39dbc150-8ce4-4a4c-bc73-7670bbf4bf28
-- title:
--   Half: top F eq
-- statement:
--   The program for the first factor of a term of a piece computes it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabKF.lean#L113-L127
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabKF.lean#L113-L127

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Definitions.Def_ClauseBound_Boson_KF
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Inst_HalfTabKF
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson
open HalfTabKF

theorem ClauseBound.Inst.Half.topF_eq {pad : U} {W h : ℕ} {flat : List (List ℕ)} {μ : List ℕ} (hW : 1 ≤ W) (hf : FlatOK W flat) (hμ : ∀ n ∈ μ, n ≤ W) (hs : μ.sum = h)
    (hp : padKF W flat.length h μ.sum μ.length ≤ pad.length) (i : ℕ) (r : ℤ) {π σ : List ℕ} (hπ : π ∈ flat) (hσ : σ ∈ flat) :
    topF pad W flat h μ i r π σ = ClauseBound.Boson.topK μ h i r ↑π ↑σ := by sorry
