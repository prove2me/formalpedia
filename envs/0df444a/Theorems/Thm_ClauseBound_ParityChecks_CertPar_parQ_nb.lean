-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertPar_parQ_nb
-- name    : ClauseBound.ParityChecks.CertPar.parQ_nb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:21:00.236499+00:00
-- url     : https://prove2.me/theorems/982023a8-fd0d-450d-aae0-d6f86faf0aaf
-- title:
--   Cert Par: par Q nb
-- statement:
--   The second parameter is nb.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L59-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L59-L59

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

theorem ClauseBound.ParityChecks.CertPar.parQ_nb (n Δ m : ℕ) : (parQ n Δ m).nb = nbOf n Δ := by sorry
