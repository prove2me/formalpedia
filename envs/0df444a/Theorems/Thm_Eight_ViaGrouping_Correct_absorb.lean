-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Correct_absorb
-- name    : Eight.ViaGrouping.Correct.absorb
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:04:34.544839+00:00
-- url     : https://prove2.me/theorems/726d7581-ea11-4d22-9912-5905481beece
-- title:
--   Correct: absorb
-- statement:
--   The bound of Lemma 1 with B + 1 and S + 2 taken up by the constant: if NA has the bound of Lemma
--   1 (`Correct`), then there is a constant A such that NA outputs the value of every network with
--   parameters P, B + 1, τ, given on states of size at most S + 2,
--   within A·2^{εU + b·gP/K}·(P + B)^A·τ steps, on states of size at most S + A·(size c + P + B)^A; by P +
--   B + 1 ≤ 2(P + B).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Bridge.lean#L131-L169
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Bridge.lean#L131-L169

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Bridge
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Finset Stepped Eight.SecNetworks
variable {g : ℕ}

theorem Eight.ViaGrouping.Correct.absorb {NA : NetAlg} {K : ℕ} {ε b : ℝ} (h : Correct NA g K ε b) :
    ∃ A : ℕ, ∀ (C : Type) [HasSize C] (Np : Procs C) (c : C) (N : Net g) (P B t S : ℕ), IsNetworkP Np c N P (B + 1) t (S + 2) →
      ∃ T : ℕ, (NA.app Np).Runs c T (S + A * (size c + P + B) ^ A) N.value ∧
        (T : ℝ) ≤ A * (2 : ℝ) ^ (ε * (N.U : ℝ) + b * ((g : ℝ) * P) / K) * ((P : ℝ) + B) ^ A * t := by sorry
