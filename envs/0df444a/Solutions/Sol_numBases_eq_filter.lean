-- Prove2me | solution 1 for numBases_eq_filter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:46:13.35612+00:00
-- url     : https://prove2.me/submissions/6ddd021a-04c2-4129-86c4-347a58bfd96b

import Definitions.Def_CARDB
import Mathlib.Combinatorics.Colex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_CARDB_SmallN

set_option autoImplicit true
open Set TopologicalSpace
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
variable {n : ℕ}
theorem _root_.solution (n : ℕ) :
    numBases n =
      ((Finset.range (2 ^ (2 ^ n))).filter fun m => isBasisNat n m = true).card := by
  rw [numBases, List.countP_eq_length_filter]
  have hnodup : ((List.range (2 ^ (2 ^ n))).filter (isBasisNat n)).Nodup :=
    List.Nodup.filter _ List.nodup_range
  rw [← List.toFinset_card_of_nodup hnodup, List.toFinset_filter, List.toFinset_range]
