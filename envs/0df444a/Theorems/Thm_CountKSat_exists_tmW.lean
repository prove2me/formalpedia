-- Prove2me | Theorems.Thm_CountKSat_exists_tmW
-- name    : CountKSat.exists_tmW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:54:12.0391+00:00
-- url     : https://prove2.me/theorems/0c2a17e4-7f5f-497e-9bdc-88690cd26d34
-- title:
--   Count KSat: exists tm W
-- statement:
--   A stepped computation `M` on bit strings whose result is a list of bits, with polynomial-time
--   init, step and out, runs on one of Mathlib's
--   multi-stack machines `N` with finite alphabets. There is one number `q` such that, whenever `M` ends
--   on `x` with the result `w` within `T` steps and with
--   all states of size at most `S`, the machine `N` started on `x` halts with output `w` within q · (T + 1)
--   · (|x| + S + 1)^q steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Host.lean#L222-L279
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Host.lean#L222-L279

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_ToTuring_Machine_Host
import Definitions.Def_CountKSat_Host
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
open CountKSat
open Groundwork Groundwork.TM Groundwork.Host Turing HostW

theorem CountKSat.exists_tmW (M : Stepped (List Bool) (List Bool)) [IsPolyT M] :
    ∃ (N : TM2ComputableAux Bool Bool) (q : ℕ), (∀ k, Finite (N.tm.Γ k)) ∧
      ∀ (x : List Bool) (T S : ℕ) (w : List Bool), M.Runs x T S w →
        Nonempty (TM2OutputsInTime N.tm (x.map N.inputAlphabet.invFun) (some (w.map N.outputAlphabet.invFun))
          (q * (T + 1) * (x.length + S + 1) ^ q)) := by sorry
