-- Prove2me | Theorems.Thm_ClauseBound_Boson_sum_aFam_eq
-- name    : ClauseBound.Boson.sum_aFam_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:39:28.485559+00:00
-- url     : https://prove2.me/theorems/a38d2c64-60b8-4ef3-8580-6bcc890d7fac
-- title:
--   Boson: sum a Fam eq
-- statement:
--   A sum over the monomials of a^μ with factors that depend only on the weight of the monomial is a
--   sum over the weights 0, …, |μ|.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/KF.lean#L175-L186
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/KF.lean#L175-L186

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

theorem ClauseBound.Boson.sum_aFam_eq (μ : List ℕ) (g : ℕ → ℤ) (r : ℤ) (π σ : Multiset ℕ) :
    ((aFam μ).map fun c => c.1 * g c.2.sum * op c.2 r π σ).sum = ∑ w ∈ range (μ.sum + 1), g w * KF μ w r π σ := by sorry
