-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Ev_sized_mono
-- name    : ClauseBound.ParityChecks.Ev.sized_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:36:17.425987+00:00
-- url     : https://prove2.me/theorems/7f624d1a-7991-444a-ac4f-2549d3fc752a
-- title:
--   Ev: sized mono
-- statement:
--   A network of size P is a network of every larger size.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Ev.lean#L44-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Ev.lean#L44-L51

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Ev
import Theorems.Thm_Groundwork_Prog_sized_mono

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Ev
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW

theorem ClauseBound.ParityChecks.Ev.sized_mono {J σ τ : Type} [Fintype J] [LinearOrder J] {N : Network J σ τ} {P P' B : ℕ} (h : N.Sized P B) (hP : P ≤ P') : N.Sized P' B := by sorry
