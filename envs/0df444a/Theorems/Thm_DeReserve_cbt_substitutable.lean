-- Prove2me | Theorems.Thm_DeReserve_cbt_substitutable
-- name    : DeReserve.cbt_substitutable
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:54.873035+00:00
-- url     : https://prove2.me/theorems/ae108084-5133-4700-b6b5-881df98f3e22
-- title:
--   Proof of Theorem 3 (pp.34–35): substitutability of $C^{BT}_s$
-- statement:
--   For every institution $s$ and membership profile $T$, every $i,j\in I$ and every $A\subseteq I\setminus\{i,j\}$:
--
--   $$i\notin C^{BT}_s(A\cup\{i\})\;\Longrightarrow\;i\notin C^{BT}_s(A\cup\{i,j\}).$$
--
--   With size monotonicity this gives strategy-proofness of DA-BT for fixed memberships (Hatfield–Milgrom 2005).
--
--   Differences from the source:
--   - encoding: strict linear orders ≻_s on I ∪ {∅} and P_i on S ∪ {∅}; ∅; membership GC → rank bijections Option I ≃ Fin (|I|+1) and Option S ≃ Fin (|S|+1) (rank 0 best); none; none : Option Res; reason: Lean convention; every strict linear order is such a bijection and conversely, so the instances are the same
--   - encoding: C^BT iterates until no OBC seat is vacant → the last iteration is searched among the first q^OBC_s + 1 iterations; reason: q^OBC strictly decreases at every non-final iteration, so the bound is never reached before termination
-- source:
--   Aygün–Turhan, How to De-reserve Reserves: Admissions to Technical Colleges in India, arXiv:2103.05899v5, Proof of Theorem 3, Substitutability, pp.34–35

import Mathlib
import Definitions.Def_DeReserve_Model

namespace DeReserve

/-- **Substitutability of `C^BT_s`.** Aygün–Turhan, *How to De-reserve Reserves*, arXiv:2103.05899v5, Proof of Theorem 3, Substitutability, pp.34–35:
for `i, j ∈ I` and `A ⊆ I \ {i, j}`, if `i ∉ C^BT_s(A ∪ {i})` then `i ∉ C^BT_s(A ∪ {i, j})`,
for every institution `s` and every membership profile `T`. -/
theorem cbt_substitutable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (q : S → Cap) (pri : S → Priority I) :
    ∀ (s : S) (T : I → CatMembership) (A : Finset I) (i j : I), i ∉ A → j ∉ A →
      i ∉ chosenBT (pri s) T (q s) (insert i A) →
      i ∉ chosenBT (pri s) T (q s) (insert j (insert i A)) := by sorry

end DeReserve
