-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Binom_choose_mul_choose_le
-- name    : ClauseBound.ParityChecks.Binom.choose_mul_choose_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:42:51.200982+00:00
-- url     : https://prove2.me/theorems/0c210d99-bdd0-44ec-8528-e77670e6bde9
-- title:
--   Binom: choose mul choose le
-- statement:
--   C(a,i)·C(b,j) ≤ C(a+b, i+j).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Binom.lean#L28-L30
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Binom.lean#L28-L30

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Binom
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open ClauseBound.ParityChecks.Binom

theorem ClauseBound.ParityChecks.Binom.choose_mul_choose_le (a b i j : ℕ) : a.choose i * b.choose j ≤ (a + b).choose (i + j) := by sorry
