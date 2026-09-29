-- Prove2me | Theorems.Thm_Erdos180_degree_eq_natCard_neighborSet
-- name    : Erdos180.degree_eq_natCard_neighborSet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T01:58:30.567503+00:00
-- url     : https://prove2.me/theorems/558c8f90-a3f4-4e78-800b-4547b661cb42
-- title:
--   Degree as a cardinal
-- statement:
--   For a vertex $v$ of a simple graph $G$ with finite neighbourhood,
--
--   $$\deg_G(v) \;=\; \#\, N_G(v).$$
--
--   The companion of the previous identity, used wherever the minimum-degree hypothesis
--   $\delta(B) \ge d$ of Lemma 3.2 is transported between formulations.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L56-L60

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.SetTheory.Cardinal.Finite

open Erdos180
open Finset SimpleGraph
open scoped Classical

theorem Erdos180.degree_eq_natCard_neighborSet {V : Type*}
    (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] :
    G.degree v = Nat.card (G.neighborSet v) := by sorry
