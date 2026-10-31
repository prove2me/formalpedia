-- Prove2me | Theorems.Thm_DeReserve_cbt_sizeMonotone
-- name    : DeReserve.cbt_sizeMonotone
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:38.062003+00:00
-- url     : https://prove2.me/theorems/88cfe8aa-66dd-42ed-a85f-c0ca2bbc3196
-- title:
--   Proof of Theorem 3 (pp.35–36): size monotonicity of $C^{BT}_s$
-- statement:
--   For every institution $s$ and membership profile $T$, every $i\in I$ and every $A\subseteq I\setminus\{i\}$:
--
--   $$|C^{BT}_s(A)|\le|C^{BT}_s(A\cup\{i\})|.$$
--
--   With substitutability this gives strategy-proofness of DA-BT for fixed memberships (Hatfield–Milgrom 2005).
--
--   Differences from the source:
--   - encoding: strict linear orders ≻_s on I ∪ {∅} and P_i on S ∪ {∅}; ∅; membership GC → rank bijections Option I ≃ Fin (|I|+1) and Option S ≃ Fin (|S|+1) (rank 0 best); none; none : Option Res; reason: Lean convention; every strict linear order is such a bijection and conversely, so the instances are the same
--   - encoding: C^BT iterates until no OBC seat is vacant → the last iteration is searched among the first q^OBC_s + 1 iterations; reason: q^OBC strictly decreases at every non-final iteration, so the bound is never reached before termination
-- source:
--   Aygün–Turhan, How to De-reserve Reserves: Admissions to Technical Colleges in India, arXiv:2103.05899v5, Proof of Theorem 3, Size monotonicity, pp.35–36

import Mathlib
import Definitions.Def_DeReserve_Model

namespace DeReserve

/-- **Size monotonicity of `C^BT_s`.** Aygün–Turhan, *How to De-reserve Reserves*, arXiv:2103.05899v5, Proof of Theorem 3, Size monotonicity,
pp.35–36: for `i ∈ I` and `A ⊆ I \ {i}`, `|C^BT_s(A)| ≤ |C^BT_s(A ∪ {i})|`, for every
institution `s` and every membership profile `T`. -/
theorem cbt_sizeMonotone {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (q : S → Cap) (pri : S → Priority I) :
    ∀ (s : S) (T : I → CatMembership) (A : Finset I) (i : I), i ∉ A →
      (chosenBT (pri s) T (q s) A).card ≤ (chosenBT (pri s) T (q s) (insert i A)).card := by sorry

end DeReserve
