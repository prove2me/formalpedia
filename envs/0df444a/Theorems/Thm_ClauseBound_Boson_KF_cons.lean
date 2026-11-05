-- Prove2me | Theorems.Thm_ClauseBound_Boson_KF_cons
-- name    : ClauseBound.Boson.KF_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:39:15.714917+00:00
-- url     : https://prove2.me/theorems/2c1205c0-f7b4-41e0-b800-f30aac9d4c4d
-- title:
--   Boson: KF cons
-- statement:
--   One more factor (−1)^{n−1}·y_n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/KF.lean#L152-L171
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/KF.lean#L152-L171

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_KF
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset

theorem ClauseBound.Boson.KF_cons (n : ℕ) (μ : List ℕ) (w : ℕ) (r : ℤ) (π σ : Multiset ℕ) :
    KF (n :: μ) w r π σ =
      ∑ j ∈ Icc 1 n, if j ≤ w then (-1) ^ (n - 1) * (n.choose j : ℤ) * nop j (KF μ (w - j)) r π σ else 0 := by sorry
