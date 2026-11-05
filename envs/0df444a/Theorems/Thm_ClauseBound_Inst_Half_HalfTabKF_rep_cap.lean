-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_HalfTabKF_rep_cap
-- name    : ClauseBound.Inst.Half.HalfTabKF.rep_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:40:20.72932+00:00
-- url     : https://prove2.me/theorems/3ce57255-7c16-43b1-8d0d-b9ce1864cfd5
-- title:
--   Half Tab KF: rep cap
-- statement:
--   h + 1 tables that have the entries of the families F 0, …, F h, bounded by 2^B, are not cut off
--   by a pad of the length given, and hold these families.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabKF.lean#L47-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabKF.lean#L47-L64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Definitions.Def_ClauseBound_Boson_KF
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Inst_HalfTabKF
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson
open ClauseBound.Inst.Half.HalfTabKF

theorem ClauseBound.Inst.Half.HalfTabKF.rep_cap {pad : U} {W h B : ℕ} {flat : List (List ℕ)} (hf : FlatOK W flat) {G : ℕ → List ℕ → List ℕ → ℤ} {F : ℕ → ℤ → Ker}
    (hG : ∀ w ≤ h, ∀ π ∈ flat, ∀ σ ∈ flat, G w π σ = F w ((π.sum : ℤ) - σ.sum) π σ)
    (hB : ∀ w r (π σ : Multiset ℕ), π.sum ≤ W → σ.sum ≤ W → |F w r π σ| ≤ 2 ^ B)
    (hp : (h + 1) * (flat.length ^ 2 * (3 * B + 10) + 4) + 2 ≤ pad.length) :
    ∀ w ≤ h, Rep flat ((cap pad [] ((List.range (h + 1)).map fun w => tab flat (G w))).getD w []) (F w) := by sorry
