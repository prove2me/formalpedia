-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertNum_numP_aux
-- name    : ClauseBound.ParityChecks.CertNum.numP_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:19:22.871139+00:00
-- url     : https://prove2.me/theorems/cd4e9af2-d2d8-4f6a-b180-0defa8c17359
-- title:
--   Cert Num: num P aux
-- statement:
--   The Cert Num construction uses the num P aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertNum.lean#L47-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertNum.lean#L47-L58

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_ClauseBound_ParityChecks_CertNum
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertNum
open Groundwork PaddedDescent.F ClauseBound.Alg.CertGridG ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]

theorem ClauseBound.ParityChecks.CertNum.numP_aux {nb i₀ : α → ℕ} {A : α → ℤ} {B : α → ℕ → ℤ} (hnb : Unary nb) (hi : Unary i₀) (hA : PolyT A) (hB : PolyT fun p : α × ℕ => B p.1 p.2) :
    PolyT fun x => A x * (nb x : ℤ) ^ i₀ x + ((List.range (i₀ x + 1)).map fun i => (-2 : ℤ) ^ i * (nb x : ℤ) ^ (i₀ x - i) * B x i).sum := by sorry
