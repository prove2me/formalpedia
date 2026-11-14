-- Prove2me | Theorems.Thm_ConsistentSubmodular_HardInstance_tinyCount_sum_le
-- name    : ConsistentSubmodular.HardInstance.tinyCount_sum_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:25:34.934203+00:00
-- url     : https://prove2.me/theorems/91258b6a-f6da-4aec-bc25-718013a96433
-- title:
--   Tiny sets of the three groups are disjoint
-- statement:
--   In the hard stream on $3k+2$ elements, let $c_g(T)$ be the number of tiny sets of group $g\in\{0,1,2\}$ contained in a family $T$ of stream elements. Then for every $T$,
--   $$c_0(T)+c_1(T)+c_2(T)\le |T|.$$
--
--   The tiny sets of the three groups are disjoint, so a family contains at most as many tiny sets as elements. This is used to bound the total number of tiny sets held by an algorithm with cardinality budget $k$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Impossibility/HardStream.lean#L157-L171 (`ConsistentSubmodular.HardInstance.tinyCount_sum_le`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Impossibility_HardStream

open scoped BigOperators
open Finset
open ConsistentSubmodular ConsistentSubmodular.HardInstance

theorem ConsistentSubmodular.HardInstance.tinyCount_sum_le {k : ℕ} (T : Finset (Fin (3 * k + 2))) :
    tinyCount k 0 T + tinyCount k 1 T + tinyCount k 2 T ≤ T.card := by sorry
