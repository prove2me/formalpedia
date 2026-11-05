-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertNum_num_aux
-- name    : ClauseBound.ParityChecks.CertNum.num_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:19:42.416893+00:00
-- url     : https://prove2.me/theorems/a5941e0f-6160-41e1-8a34-f4d5700d7cfa
-- title:
--   Cert Num: num aux
-- statement:
--   The Cert Num construction uses the num aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertNum.lean#L129-L150
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertNum.lean#L129-L150

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_ClauseBound_ParityChecks_CertNum
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertNum
open Groundwork PaddedDescent.F ClauseBound.Alg.CertGridG ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]

theorem ClauseBound.ParityChecks.CertNum.num_aux {m nb r i₀ j nI nR nC : α → ℕ} {nP : α → ℤ} (hm : Unary m) (hnb : Unary nb) (hr : Unary r) (hi : Unary i₀) (hj : PolyT j) (hP : PolyT nP)
    (hI : PolyT nI) (hR : PolyT nR) (hC : PolyT nC) :
    PolyT fun x => (5 : ℤ) ^ (r x - 1 - j x) * nP x * ((8 * m x * r x * (nb x + 1) ^ (m x + r x) : ℕ) : ℤ) +
      ((nI x * (2 * 8 ^ (r x - 1 - j x) * nb x ^ i₀ x * (nb x + 1) ^ (m x + r x)) +
        nR x * (2 * 8 ^ (r x - 1 - j x) * nb x ^ i₀ x * m x * (nb x + 1) ^ r x) +
        nC x * (2 * 8 ^ (r x - 1 - j x) * nb x ^ i₀ x * r x * (nb x + 1) ^ m x) : ℕ) : ℤ) := by sorry
