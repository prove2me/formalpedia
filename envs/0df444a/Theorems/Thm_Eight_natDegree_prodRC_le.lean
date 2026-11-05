-- Prove2me | Theorems.Thm_Eight_natDegree_prodRC_le
-- name    : Eight.natDegree_prodRC_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:41:56.501089+00:00
-- url     : https://prove2.me/theorems/ff7978d8-35b2-42b0-9615-67ac5c96a69b
-- title:
--   Eight: nat Degree prod RC le
-- statement:
--   «The t factors are polynomials in T of degree at most 1», so the product has degree at most t.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L62-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L62-L64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_Blocks
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_PiecesAC
set_option autoImplicit false
section
section
open Eight
open Finset Polynomial

theorem Eight.natDegree_prodRC_le {lam : ℕ} (x y u v : Pieces.Bits lam) : (prodRC x y u v).natDegree ≤ tOf lam := by sorry
