-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_partH_eq
-- name    : ClauseBound.Inst.Half.partH_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:40:16.895496+00:00
-- url     : https://prove2.me/theorems/62897c80-0d64-4bd2-bd71-78d5668e0b06
-- title:
--   Half: part H eq
-- statement:
--   What `partH c₀ top` returns on two strings of λ bits and a label θ, with h = `hF c₀ λ`, s =
--   `sOf h i` and T the table of all partitions of 0, …, 4h: the value `valK` at the pair number θ
--   of the list of labels, or 0 if there is no such pair. The pad has length at least `padLen h`, and
--   the partitions of the two strings are listed and have weight h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfVal.lean#L99-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfVal.lean#L99-L112

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfVal
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec Finset
open Val

theorem ClauseBound.Inst.Half.partH_eq (hT : StTopF) (hB : StBotF) {c₀ lam : ℕ} {pad : U} (hp : padLen (hF c₀ lam) ≤ pad.length) (tr top : Bool) (h' i : ℕ)
    (a b : Pieces.Bits lam) (θ : List Bool)
    (ha : encF (allTab (4 * hF c₀ lam)) (hF c₀ lam) (bitsOf a) ∈ (allTab (4 * hF c₀ lam)).flatten ∧
      (encF (allTab (4 * hF c₀ lam)) (hF c₀ lam) (bitsOf a)).sum = hF c₀ lam)
    (hb : encF (allTab (4 * hF c₀ lam)) (hF c₀ lam) (bitsOf b) ∈ (allTab (4 * hF c₀ lam)).flatten ∧
      (encF (allTab (4 * hF c₀ lam)) (hF c₀ lam) (bitsOf b)).sum = hF c₀ lam) :
    partH c₀ top ((pad, tr), (h', i), (bitsOf a, bitsOf b, θ)) =
      ((labs (allTab (4 * hF c₀ lam)) tr (hF c₀ lam) (sOf (hF c₀ lam) i))[ofWord θ]?).elim 0
        (valK tr top (hF c₀ lam) (sOf (hF c₀ lam) i) (encF (allTab (4 * hF c₀ lam)) (hF c₀ lam) (bitsOf a))
          (encF (allTab (4 * hF c₀ lam)) (hF c₀ lam) (bitsOf b))) := by sorry
