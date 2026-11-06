-- Prove2me | Theorems.Thm_Eight_Level_Cert_tOf_unary
-- name    : Eight.Level.Cert.tOf_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:19:31.189001+00:00
-- url     : https://prove2.me/theorems/121670f3-4173-4432-8757-df1c0b1c1e8f
-- title:
--   Cert: t Of unary
-- statement:
--   t = ⌈λ/3⌉ in unary, for λ in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Level/Cert.lean#L38-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Level/Cert.lean#L38-L38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_Alg_CertLevel
import Definitions.Def_ToTuring_Poly_GridSide
import Definitions.Def_Eight_Level_Cert
set_option autoImplicit false
section
section
open Eight Eight.Level
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg Stepped
open Eight.Level.Cert
variable {C : Type} [Enc C] {lam : C → ℕ}

theorem Eight.Level.Cert.tOf_unary (hl : Unary lam) : Unary fun c => tOf (lam c) := by sorry
