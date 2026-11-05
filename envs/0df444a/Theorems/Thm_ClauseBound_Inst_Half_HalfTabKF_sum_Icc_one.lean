-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_HalfTabKF_sum_Icc_one
-- name    : ClauseBound.Inst.Half.HalfTabKF.sum_Icc_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:39:16.058088+00:00
-- url     : https://prove2.me/theorems/682ee69e-8a40-4202-ad35-728d5662fd88
-- title:
--   Half Tab KF: sum Icc one
-- statement:
--   A sum over 1, …, n as a sum over 0, …, n − 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabKF.lean#L31-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabKF.lean#L31-L34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Definitions.Def_ClauseBound_Boson_KF
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Inst_HalfTabKF
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson
open ClauseBound.Inst.Half.HalfTabKF

theorem ClauseBound.Inst.Half.HalfTabKF.sum_Icc_one (f : ℕ → ℤ) (n : ℕ) : ∑ j ∈ Icc 1 n, f j = ∑ i ∈ range n, f (i + 1) := by sorry
