-- Prove2me | Theorems.Thm_CassandrasLafortune_parallel_run_iff
-- name    : CassandrasLafortune.parallel_run_iff
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-22T18:52:51.866828+00:00
-- url     : https://prove2.me/theorems/2de5b859-f04a-4199-b432-edbac6273529
-- title:
--   Reached states of projected traces
-- statement:
--   The parallel generator reaches the pair $(q,r)$ from its initial state exactly when the left projected trace reaches $q$ and the right projected trace reaches $r$ from their respective initial states.
-- source:
--   C. G. Cassandras and S. Lafortune, Introduction to Discrete Event Systems, 2nd ed. (Springer, 2008), ch. 2, §2.3.2, Composition Operations, parallel composition. https://doi.org/10.1007/978-0-387-68612-7_2 Lean proof https://github.com/kmehltretter82/linux-rv-lean/blob/d516e69a81f09c0a017196ea954e4676316cfa3f/LinuxRV/Parallel.lean#L36

import Definitions.Def_CassandrasLafortune_Parallel
open RamadgeWonham.Shared

namespace CassandrasLafortune
variable {A B C : Type}
theorem parallel_run_iff (G : Generator (A ⊕ C)) (H : Generator (B ⊕ C))
    (w : List (Event A B C)) (q : G.Q) (r : H.Q) :
    (parallel G H).run w = some (q, r) ↔
      G.run (w.filterMap Event.left) = some q ∧ H.run (w.filterMap Event.right) = some r := by sorry
end CassandrasLafortune
