-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_kfEntry_polyT
-- name    : ClauseBound.Inst.Half.kfEntry_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:05.49054+00:00
-- url     : https://prove2.me/theorems/5909af8f-7611-4535-a289-c971baa53517
-- title:
--   Half: kf Entry poly T
-- statement:
--   One entry of one table of the next round.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L90-L99
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L90-L99

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTab
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_CertHalfTab
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Inst.Rec
variable {α : Type} [Enc α]

theorem ClauseBound.Inst.Half.kfEntry_polyT {W n w : α → ℕ} {flat : α → List (List ℕ)} {S : α → List (List ℤ)} {π σ : α → List ℕ} (hW : Unary W) (hn : PolyT n)
    (hw : PolyT w) (hf : PolyT flat) (hS : PolyT S) (hπ : PolyT π) (hσ : PolyT σ) :
    PolyT fun x => sumR (min (n x) (W x)) fun j =>
      if j + 1 ≤ w x then sgnZ ((n x - 1 : ℕ) : ℤ) * chooseZ (n x : ℤ) (j + 1) * nopE (W x) (j + 1) (flat x) ((S x).getD (w x - (j + 1)) []) (π x) (σ x)
      else 0 := by sorry
