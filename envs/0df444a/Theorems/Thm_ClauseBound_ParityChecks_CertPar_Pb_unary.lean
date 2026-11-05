-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertPar_Pb_unary
-- name    : ClauseBound.ParityChecks.CertPar.Pb_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:21:06.282756+00:00
-- url     : https://prove2.me/theorems/2038a6f6-b89e-43ef-b24e-ff38f350e25d
-- title:
--   Cert Par: Pb unary
-- statement:
--   The bound for the size of a network of marks is given in unary if its arguments are.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L120-L121
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L120-L121

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

theorem ClauseBound.ParityChecks.CertPar.Pb_unary {g n β Δ : α → ℕ} (hg : Unary g) (hn : Unary n) (hβ : Unary β) (hΔ : Unary Δ) : Unary fun x => Pb (g x) (n x) (β x) (Δ x) := by sorry
