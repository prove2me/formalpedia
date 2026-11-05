-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Spec_padLen_le
-- name    : ClauseBound.Inst.Half.Spec.padLen_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:38:05.682591+00:00
-- url     : https://prove2.me/theorems/86df1829-e521-4d15-b1e0-ce53f0f4d653
-- title:
--   Spec: pad Len le
-- statement:
--   A pad of length 2^{cλ} is long enough for all tables.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfSpec.lean#L56-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfSpec.lean#L56-L58

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfSpec
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec Finset
open ClauseBound.Inst.Half.Spec

theorem ClauseBound.Inst.Half.Spec.padLen_le {c₀ c lam : ℕ} (hC : Cst c₀ c lam) : padLen (ClauseBound.Part.hOf lam) ≤ 2 ^ (c * lam) := by sorry
