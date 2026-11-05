-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_tabKF_rep
-- name    : ClauseBound.Inst.Half.tabKF_rep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:39:30.843685+00:00
-- url     : https://prove2.me/theorems/4eca4899-6145-439e-902e-e0d1d6c57671
-- title:
--   Half: tab KF rep
-- statement:
--   The table number w holds the matrices of (the part of weight w of a^μ)[r].
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabKF.lean#L90-L110
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabKF.lean#L90-L110

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

theorem ClauseBound.Inst.Half.tabKF_rep {pad : U} {W h : ℕ} {flat : List (List ℕ)} {μ : List ℕ} (hW : 1 ≤ W) (hf : FlatOK W flat) (hμ : ∀ n ∈ μ, n ≤ W)
    (hp : padKF W flat.length h μ.sum μ.length ≤ pad.length) : ∀ w ≤ h, Rep flat ((tabKF pad W flat h μ).getD w []) (ClauseBound.Boson.KF μ w) := by sorry
