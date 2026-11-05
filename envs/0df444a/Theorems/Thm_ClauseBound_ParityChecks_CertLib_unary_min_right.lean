-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertLib_unary_min_right
-- name    : ClauseBound.ParityChecks.CertLib.unary_min_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:21:26.26347+00:00
-- url     : https://prove2.me/theorems/f2942328-65f6-47f0-8232-d4cd109cca7a
-- title:
--   Cert Lib: unary min right
-- statement:
--   The smaller of any number and a number given in unary is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L35-L36
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L35-L36

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Theorems.Thm_ClauseBound_Alg_CertGridG_unary_min_right

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertLib
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]

theorem ClauseBound.ParityChecks.CertLib.unary_min_right {f g : α → ℕ} (hf : PolyT f) (hg : Unary g) : Unary fun x => min (f x) (g x) := by sorry
