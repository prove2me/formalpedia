-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_div_congr
-- name    : ClauseBound.ParityChecks.div_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:04:24.252136+00:00
-- url     : https://prove2.me/theorems/2afaa882-b401-4cfa-9994-eb50a1954fd9
-- title:
--   Parity Checks: div congr
-- statement:
--   If a ≡ 2^r·b modulo 2^{β+r}, then a/2^r ≡ b modulo 2^β (the division is exact).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Congr.lean#L51-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Congr.lean#L51-L60

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Congr
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Congr
variable {X : Type} [Fintype X] {m : ℕ} (V : X → Finset (Fin m)) (nb r : ℕ)

theorem ClauseBound.ParityChecks.div_congr {β r : ℕ} {a b : ℤ} (h : a ≡ 2 ^ r * b [ZMOD 2 ^ (β + r)]) : a / 2 ^ r ≡ b [ZMOD 2 ^ β] := by sorry
