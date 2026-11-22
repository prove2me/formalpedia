-- Prove2me | Theorems.Thm_CassandrasLafortune_first_failure_iff
-- name    : CassandrasLafortune.first_failure_iff
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-22T18:53:20.241529+00:00
-- url     : https://prove2.me/theorems/03cb86f4-bb27-4667-b39f-8075a2de210b
-- title:
--   First blocked event after a legal prefix
-- statement:
--   If a prefix reaches $(q,r)$, adjoining one event fails exactly when a participant has no transition at that state on its local event. Either or both participants can block a shared event.
-- source:
--   C. G. Cassandras and S. Lafortune, Introduction to Discrete Event Systems, 2nd ed. (Springer, 2008), ch. 2, §2.3.2, Composition Operations, parallel composition. https://doi.org/10.1007/978-0-387-68612-7_2 Monitoring corollary derived from the construction. Lean proof https://github.com/kmehltretter82/linux-rv-lean/blob/d516e69a81f09c0a017196ea954e4676316cfa3f/LinuxRV/Parallel.lean#L80

import Definitions.Def_CassandrasLafortune_Parallel
open RamadgeWonham.Shared

namespace CassandrasLafortune
variable {A B C : Type}
theorem first_failure_iff (G : Generator (A ⊕ C)) (H : Generator (B ⊕ C))
    (pre : List (Event A B C)) (e : Event A B C) (q : G.Q) (r : H.Q)
    (hpre : (parallel G H).run pre = some (q, r)) :
    (parallel G H).run (pre ++ [e]) = none ↔
      (∃ a, e.left = some a ∧ G.δ a q = none) ∨ (∃ b, e.right = some b ∧ H.δ b r = none) := by sorry
end CassandrasLafortune
