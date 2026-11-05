-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertLib_sup_range_unary_min
-- name    : ClauseBound.ParityChecks.CertLib.sup_range_unary_min
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:19:50.899774+00:00
-- url     : https://prove2.me/theorems/a92bdc74-6f7a-467d-abed-e54145296096
-- title:
--   Cert Lib: sup range unary min
-- statement:
--   The largest of f 0, …, f (n − 1) is given in unary if n and the numbers are; the numbers are
--   only needed for indices given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L172-L175
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L172-L175

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

theorem ClauseBound.ParityChecks.CertLib.sup_range_unary_min {n : α → ℕ} {f : α → ℕ → ℕ} (hn : Unary n) (hf : Unary fun p : α × ℕ => f p.1 (min p.2 (n p.1))) :
    Unary fun x => (Finset.range (n x)).sup (f x) := by sorry
