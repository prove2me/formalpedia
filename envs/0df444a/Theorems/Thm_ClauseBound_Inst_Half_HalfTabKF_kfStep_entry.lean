-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_HalfTabKF_kfStep_entry
-- name    : ClauseBound.Inst.Half.HalfTabKF.kfStep_entry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:40:40.353674+00:00
-- url     : https://prove2.me/theorems/01b9110b-dfd0-4148-9b3f-03ce3c1f2693
-- title:
--   Half Tab KF: kf Step entry
-- statement:
--   One round of the program is the recursion for one more factor.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabKF.lean#L74-L83
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabKF.lean#L74-L83

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Definitions.Def_ClauseBound_Boson_KF
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Inst_HalfTabKF
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson
open ClauseBound.Inst.Half.HalfTabKF

theorem ClauseBound.Inst.Half.HalfTabKF.kfStep_entry {W h n w : ℕ} {flat : List (List ℕ)} {S : List (List ℤ)} {μ : List ℕ} (hf : FlatOK W flat) (hn : n ≤ W)
    (hS : ∀ w ≤ h, Rep flat (S.getD w []) (KF μ w)) (hw : w ≤ h) {π σ : List ℕ} (hπ : π ∈ flat) (hσ : σ ∈ flat) :
    (sumR (min n W) fun j =>
      if j + 1 ≤ w then sgnZ ((n - 1 : ℕ) : ℤ) * chooseZ (n : ℤ) (j + 1) * nopE W (j + 1) flat (S.getD (w - (j + 1)) []) π σ else 0) =
      KF (n :: μ) w ((π.sum : ℤ) - σ.sum) π σ := by sorry
