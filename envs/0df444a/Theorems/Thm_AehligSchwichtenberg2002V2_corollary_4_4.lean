-- Prove2me | Theorems.Thm_AehligSchwichtenberg2002V2_corollary_4_4
-- name    : AehligSchwichtenberg2002V2.corollary_4_4
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-21T06:57:10.863046+00:00
-- url     : https://prove2.me/theorems/675a1963-57c1-406a-8618-7615bc4fb4e5
-- title:
--   Corollary 4.4 — Non-size-increasing property on binary lists
-- statement:
--   Let $f$ be a closed term of type $L(B)\multimap L(B)$. If applying $f$ to a canonical binary list of length $n$ reduces to a normal term, that term is a list of length at most $n$.
-- source:
--   Klaus Aehlig and Helmut Schwichtenberg (2002), A syntactical analysis of non-size-increasing polynomial time computation, Corollary 4.4, binary-list case. https://arxiv.org/abs/cs/0011037

import Definitions.Def_AehligSchwichtenberg2002V2_Bounds

namespace AehligSchwichtenberg2002V2

/-- The binary-list case of Corollary 4.4 (p. 11).
A closed `f : L(B) ⊸ L(B)` applied to a canonical list with `n` entries reduces to
no normal form other than a list with at most `n` entries. -/
theorem corollary_4_4 {f l w : Term} {n : Nat}
    (hf : HasType [] f (.lolli Ty.bin Ty.bin))
    (hl : IsCanonicalListInput .bool l n)
    (hred : RedStar (.app f l) w)
    (hnorm : IsNormal w) :
    ∃ m : Nat, listEntryCount w = some m ∧ m ≤ n := by sorry

end AehligSchwichtenberg2002V2
