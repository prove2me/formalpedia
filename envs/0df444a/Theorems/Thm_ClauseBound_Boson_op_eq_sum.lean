-- Prove2me | Theorems.Thm_ClauseBound_Boson_op_eq_sum
-- name    : ClauseBound.Boson.op_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:19:36.429143+00:00
-- url     : https://prove2.me/theorems/03785dc7-df33-4f37-af85-b35aa5d046cc
-- title:
--   Boson: op eq sum
-- statement:
--   The entry of the matrix defined by recursion is the coefficient of t^π in a[r]·t^σ, with a[r]
--   the sum over tuples of the paper.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Text.lean#L197-L247
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Text.lean#L197-L247

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_WickPlus
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_Text
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset MvPolynomial
open Text

theorem ClauseBound.Boson.op_eq_sum (a : List ℕ) : ∀ (r : ℤ) (π σ : Multiset ℕ) (M : ℕ), 0 ∉ π → 0 ∉ σ → π.sum ≤ M → σ.sum ≤ M →
    op a r π σ = ∑ ks ∈ tup M a.length with ks.sum = -r, wt a ks * coef π (nord ks (mon σ)) := by sorry
