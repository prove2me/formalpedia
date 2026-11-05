-- Prove2me | Theorems.Thm_Eight_stPoly
-- name    : Eight.stPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:56:32.174192+00:00
-- url     : https://prove2.me/theorems/e385e955-c478-4486-aaf5-0c972fd44306
-- title:
--   Eight: st Poly
-- statement:
--   **Lemma 2 of the paper**, «computable in time poly(λ)», said there of A_i in (a) and of the
--   functions of both factorizations in (b): the program `aMul` is one polynomial-time function of (i in
--   binary, the four strings as
--   lists of bits), and `fTop` and `fBot` are polynomial-time functions of (direction, i in binary, two
--   strings and θ as lists of bits). Same as in the paper, with «time poly(λ)» read as: polynomial in
--   the length of the input, on a
--   multi-stack machine of Mathlib; for i ≤ t and θ of at most 2λ bits that is polynomial in λ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Cert.lean#L241-L241
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Cert.lean#L241-L241

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_PolyDefs
import Definitions.Def_Eight_SecCrossing_MulOut
import Definitions.Def_SingleBitPieces_SecCrossing_PolyA
import Definitions.Def_ToTuring_Lib_Table
import Definitions.Def_Eight_SecCrossing_Cert
set_option autoImplicit false
section
section
open Eight
open Groundwork PaddedDescent.F ClauseBound.Alg SingleBitPieces.SecCrossing_PolyA
open SecCrossing_Cert

theorem Eight.stPoly : StPoly := by sorry
