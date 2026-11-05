-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_pzF_polyT
-- name    : ClauseBound.Inst.Half.pzF_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:31:28.881779+00:00
-- url     : https://prove2.me/theorems/39a51851-57a1-49a0-a10f-ebccf6d09a4a
-- title:
--   Half: pz F poly T
-- statement:
--   Reading a table of numbers at an integer.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfPart.lean#L75-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfPart.lean#L75-L76

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfPart
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_CertHalfPart
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions
variable {α : Type} [Enc α]

theorem ClauseBound.Inst.Half.pzF_polyT {T : α → List ℕ} {E : α → ℤ} (hT : PolyT T) (hE : PolyT E) : PolyT fun x => pzF (T x) (E x) := by sorry
