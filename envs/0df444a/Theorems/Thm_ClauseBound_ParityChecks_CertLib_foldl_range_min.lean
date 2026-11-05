-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertLib_foldl_range_min
-- name    : ClauseBound.ParityChecks.CertLib.foldl_range_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:20:07.564578+00:00
-- url     : https://prove2.me/theorems/b289ec19-2b20-484c-8f82-b3b22b9823e7
-- title:
--   Cert Lib: foldl range min
-- statement:
--   A fold over 0, …, n − 1 only needs its step for indices at most n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L178-L179
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L178-L179

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_ParityChecks_CertLib
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertLib
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]

theorem ClauseBound.ParityChecks.CertLib.foldl_range_min {γ : Type} (n : ℕ) (g : γ → ℕ → γ) (a : γ) : (List.range n).foldl (fun c i => g c (min i n)) a = (List.range n).foldl g a := by sorry
