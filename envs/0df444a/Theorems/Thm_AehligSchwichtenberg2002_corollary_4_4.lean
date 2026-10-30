-- Prove2me | Theorems.Thm_AehligSchwichtenberg2002_corollary_4_4
-- name    : AehligSchwichtenberg2002.corollary_4_4
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T01:57:08.323908+00:00
-- url     : https://prove2.me/theorems/ee8fa0d7-cd23-4f23-8a0e-f01805651c6e
-- title:
--   Corollary 4.4: Constructor Bound on Normal Forms of Base Type
-- statement:
--   If `r : B` reduces to a normal form `v`, then the number of constructors in `v` is bounded by `|r|_{d(r)}`.
-- source:
--   Klaus Aehlig and Helmut Schwichtenberg, 'A syntactical analysis of non-size-increasing polynomial time computation', ACM Transactions on Computational Logic 3(3), 2002, pp. 383-401 (LICS 2000, pp. 84-91; doi:10.1145/507382.507386). Corollary 4.4, p. 396.

import Definitions.Def_AehligSchwichtenberg2002_Bounds

namespace AehligSchwichtenberg2002

theorem corollary_4_4 {τ : Ty} {f l w : Term} {n : Nat}
    (hf : HasType [] f (.lolli (.list τ) (.list τ)))
    (hl : IsCanonicalListInput τ l n)
    (hred : RedStar (.app f l) w)
    (hnorm : IsNormal w) :
    ∃ m : Nat, listEntryCount w = some m ∧ m ≤ n := by sorry

end AehligSchwichtenberg2002
