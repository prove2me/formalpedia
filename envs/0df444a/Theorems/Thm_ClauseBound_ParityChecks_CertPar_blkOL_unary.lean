-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertPar_blkOL_unary
-- name    : ClauseBound.ParityChecks.CertPar.blkOL_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:33:02.763819+00:00
-- url     : https://prove2.me/theorems/1e8514bf-69e4-408c-97bf-1bdce35e9bd0
-- title:
--   Cert Par: blk OL unary
-- statement:
--   The length of the blocks of the code is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L103-L104
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L103-L104

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

theorem ClauseBound.ParityChecks.CertPar.blkOL_unary {Δ : α → ℕ} (hΔ : Unary Δ) : Unary fun x => blkOL (Δ x) := by sorry
