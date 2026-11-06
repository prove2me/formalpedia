-- Prove2me | Theorems.Thm_Eight_ViaGrouping_netAlg_correct
-- name    : Eight.ViaGrouping.netAlg_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:01:41.393773+00:00
-- url     : https://prove2.me/theorems/b7e7410b-b2b1-4d81-b8c1-ff8e3a2946aa
-- title:
--   Via Grouping: net Alg correct
-- statement:
--   The bound of Lemma 1 for the algorithm of its proof, on networks on [g], for every g ≥ K for
--   which the search finds a good grouping (hypothesis `hS`; for g = 3K⁸ this is `StSearch`). K need not
--   divide 2g. The proof runs through the paragraphs «The algorithm» and «Cost»:
--   the search (`searchP_runs`), the call of the algorithm for cliques (`Cost.run_clique`), «the bound
--   follows» (`Cost.bound_follows`), and the same for the sizes of the states
--   (`Groundwork.RebalanceArith.size_le`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Main.lean#L236-L286
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Main.lean#L236-L286

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Search
import Definitions.Def_StepMachines_Math_RebalanceArith
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Main
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Cost

theorem Eight.ViaGrouping.netAlg_correct (hT : StTable) (hV : StValue) {K g : ℕ} {e : ℝ} {E : Paper.CliqueAlgorithm} (hK : 2 ≤ K) (hKg : K ≤ g) (h0 : 0 ≤ e) (h : E.Within K e)
    (hS : ∀ (C : Type) [HasSize C] (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
      ∃ x < K ^ g, (List.range (K ^ g)).find? (fun x => goodP K g Np (c, x)) = some x ∧ Good N.c P (Paper.grouping (g := g) (by omega : 0 < K) x)) :
    Correct (netAlg K g E) g K e (e + 2) := by sorry
