-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Cost_run_clique
-- name    : Eight.ViaGrouping.Cost.run_clique
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T02:24:01.07355+00:00
-- url     : https://prove2.me/theorems/2b6ee4f5-ecea-4c74-a6ce-e9e3f4225cd3
-- title:
--   Cost: run clique
-- statement:
--   «Run the algorithm for (K, e) with L, B' in the roles of λ, B; this is legitimate because
--   Definition 4 covers all integer tables. Answer each of its at most C·2^{eK²L}(B' + L)^C queries by
--   computing the entry.» For a good grouping number x, the algorithm E for
--   cliques, run with L and with `tableM` as the procedure that answers its queries, returns the value
--   of the network within A·2^{eK²L}·(B' + L)^A·t' steps, where t' = c₁·2^{P·⌊2g/K⌋}·τ is the cost of
--   one entry. A is the constant of E (the paper's C), c₁ that of `StTable`.
--   In the form of Definition 4 that this development uses, a query costs t' steps and the bound carries
--   the factor t'.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Main.lean#L201-L222
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Main.lean#L201-L222

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Search
import Definitions.Def_StepMachines_Math_RebalanceArith
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Main
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Cost

theorem Eight.ViaGrouping.Cost.run_clique (hT : StTable) (hV : StValue) {K : ℕ} (g : ℕ) {e : ℝ} {E : Paper.CliqueAlgorithm} (hK0 : 0 < K) (hg : 1 ≤ g) (h : E.Within K e) :
    ∃ A c₁ : ℕ, 1 ≤ c₁ ∧ ∀ (C : Type) [HasSize C] (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
      ∀ x < K ^ g, Good N.c P (Paper.grouping hK0 x) →
      ∃ TE : ℕ, (E.app (lamP K g Np) (tableM K g Np)).Runs (c, x) TE
          (S + c₁ * (size c + P + B) ^ c₁ + A * (size (c, x) + Bp K g P B + Paper.groupedLength K g N.U P) ^ A) N.value ∧
        (TE : ℝ) ≤ A * (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * (Paper.groupedLength K g N.U P : ℝ)) * ((Bp K g P B : ℝ) + (Paper.groupedLength K g N.U P : ℝ)) ^ A
          * ((c₁ * 2 ^ (P * (2 * g / K)) * τ : ℕ) : ℝ) := by sorry
