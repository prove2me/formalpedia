-- Prove2me | Theorems.Thm_Bagaria_kunen_no_segment_embedding
-- name    : Bagaria.kunen_no_segment_embedding
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-19T23:12:40.177735+00:00
-- url     : https://prove2.me/theorems/1e0fe656-d6c1-40bb-b8b8-ceb998307ce4
-- title:
--   Kunen: no elementary self-embedding of a two-step rank segment
-- statement:
--   Kunen's inconsistency theorem in its bounded form (slide 8): assuming the universe satisfies ZF, there is no non-trivial elementary self-embedding of the two-step rank segment below the double successor of any ordinal l — the abstract analogue of V_{l+2}. This is the obstacle that rules out Reinhardt cardinals under the Axiom of Choice, and the boundary within which the choiceless hierarchies of the source live.
-- source:
--   Bagaria (2017), Large Cardinals beyond Choice, AILA XXVI slides, p. 8, Theorem (Kunen); Kunen (1971), On the Question of the Existence of a Nontrivial Elementary Embedding of V into V, J. Symbolic Logic 36

import Mathlib
import Definitions.Def_Bagaria_arena
import Definitions.Def_Bagaria_reinhardt
import Definitions.Def_Bagaria_berkeley

universe v

namespace Bagaria

open Universe

/-- Kunen's inconsistency in the bounded segment form (slide 8): assuming
the universe satisfies ZF, there is no non-trivial elementary
self-embedding of the two-step rank segment below the double successor of
any ordinal l — the abstract analogue of V_{l+2}. -/
theorem kunen_no_segment_embedding (U : Universe.{v}) (hZF : SatisfiesZF U.mem)
    (l : Ordinal.{v}) :
    ¬ ∃ j : U.segmentOfSuccSucc l → U.segmentOfSuccSucc l,
      j ≠ id ∧
        IsElementaryOf (U.segmentMem (U.succ (U.succ l)))
          (U.segmentMem (U.succ (U.succ l))) j := by
  sorry

end Bagaria
