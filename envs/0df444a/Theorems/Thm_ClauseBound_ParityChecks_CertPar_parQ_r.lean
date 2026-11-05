-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertPar_parQ_r
-- name    : ClauseBound.ParityChecks.CertPar.parQ_r
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:20:59.343465+00:00
-- url     : https://prove2.me/theorems/eb5635b2-0d5c-4848-9f28-ad8dd5073717
-- title:
--   Cert Par: par Q r
-- statement:
--   The number of checks is 0 if m ≤ nb.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L61-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L61-L61

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_ClauseBound_ParityChecks_CertPar
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertPar
open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]

theorem ClauseBound.ParityChecks.CertPar.parQ_r (n Δ m : ℕ) : (parQ n Δ m).r = if m ≤ nbOf n Δ then 0 else rOf n (beta0 m (nbOf n Δ)) := by sorry
