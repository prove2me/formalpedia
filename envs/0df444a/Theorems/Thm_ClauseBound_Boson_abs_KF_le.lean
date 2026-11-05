-- Prove2me | Theorems.Thm_ClauseBound_Boson_abs_KF_le
-- name    : ClauseBound.Boson.abs_KF_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:39:19.305189+00:00
-- url     : https://prove2.me/theorems/3c00bbbf-e08e-444d-a97e-8d87f6ef2327
-- title:
--   Boson: abs KF le
-- statement:
--   Sizes: as for a single monomial, times the sum of the absolute values of the coefficients.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/KF.lean#L189-L205
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/KF.lean#L189-L205

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_KF
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset

theorem ClauseBound.Boson.abs_KF_le {W : ℕ} (hW : 1 ≤ W) (μ : List ℕ) (hμ : ∀ n ∈ μ, n ≤ W) (w : ℕ) (r : ℤ) {π σ : Multiset ℕ} (hπ : π.sum ≤ W) (hσ : σ.sum ≤ W) :
    |KF μ w r π σ| ≤ 2 ^ (μ.sum + (4 * W + 1) * μ.length) := by sorry
