-- Prove2me | Theorems.Thm_Exits_correct_of_searchStops
-- name    : Exits.correct_of_searchStops
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:33:44.320775+00:00
-- url     : https://prove2.me/theorems/e0a37024-c5a2-4a24-ac5d-5b6a9db0acf8
-- title:
--   Exits: correct of search Stops
-- statement:
--   The bound of Lemma 1 for the algorithm of its proof with the search of line 10, on networks on
--   [g], for every g ≥ K for which a good grouping is found (hypothesis `hS`). The proof runs through
--   the paragraphs «The algorithm» and «Cost»: «Go through all K^g groupings (a constant) and fix the
--   first good one» (`hR`: the search halts there), «Run the algorithm for (K, e) with L, B' in the
--   roles of λ, B» (`Cost.run_clique`), «the bound follows» (`Cost.bound_follows`), and the same for the
--   sizes of the states.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Grouping.lean#L68-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Grouping.lean#L68-L117

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_AlgDefs
import Definitions.Def_Eight_ViaGrouping_Main
import Definitions.Def_Eight_ViaGrouping_Keeps
import Definitions.Def_ToTuring_Poly_Range
import Mathlib.Tactic.GCongr
import Definitions.Def_Exits_Grouping
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea


set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Stepped Finset Paper Eight Eight.SecNetworks Eight.ViaGrouping Eight.ViaGrouping.Cost

theorem Exits.correct_of_searchStops (hR : StSearchStops) (hT : ViaGrouping.StTable) (hV : ViaGrouping.StValue) {K g : ℕ} {e : ℝ} {E : CliqueAlgorithm} (hK : 2 ≤ K) (hKg : K ≤ g) (h0 : 0 ≤ e) (h : E.Within K e)
    (hS : ∀ (C : Type) [HasSize C] (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
      ∃ x < K ^ g, (List.range (K ^ g)).find? (fun x => goodP K g Np (c, x)) = some x ∧ Good N.c P (Paper.grouping (g := g) (by omega : 0 < K) x)) :
    Correct (netAlg K g E) g K e (e + 2) := by sorry
