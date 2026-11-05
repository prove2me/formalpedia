-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_needG_succ
-- name    : ClauseBound.Gen.Rate.needG_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:23:28.075482+00:00
-- url     : https://prove2.me/theorems/6ab17b1c-cefd-47e1-a574-01b52661df22
-- title:
--   Rate: need G succ
-- statement:
--   The exponent at level ℓ + 1, written out.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L149-L158
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L149-L158

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_RateAux
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_ClauseBound_Gen_Rate
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}

theorem ClauseBound.Gen.Rate.needG_succ (P : PiecesF) (x₀ l Kup lam B cnt z : ℕ) : needG P Kup lam B cnt z (sched P x₀ (l + 1)) =
    max (max (Nat.size (cnt * instLen Kup lam B + 8 * z + 4 * lam + 40)) (max lam (max (Nat.size B) (Nat.size Kup))))
      (max (max (max (P.need 0 lam) (Nat.size (nPat P (step P x₀ l) lam)))
          (max (g x₀ l * Nat.size (K x₀ l)) (P.m * (g x₀ l * g x₀ l ^ 2 * lam) * (2 * g x₀ l / K x₀ l + 1))))
        (max (max ((K x₀ l - 1) * lamNextG P (step P x₀ l) lam) 0)
          (needG P (K x₀ l) (lamNextG P (step P x₀ l) lam) (bNextG P (step P x₀ l) lam B) (cnt * nPat P (step P x₀ l) lam)
            (z + nRectG (g x₀ l) (g x₀ l) * Nat.size (P.d 0 lam) + Nat.size (cnt * nPat P (step P x₀ l) lam) + (g x₀ l * g x₀ l) ^ 2 * lam +
              g x₀ l ^ 2 * (g x₀ l * B + g x₀ l ^ 2 * P.bits 0 lam + 1) + 2) (sched P x₀ l)))) := by sorry
