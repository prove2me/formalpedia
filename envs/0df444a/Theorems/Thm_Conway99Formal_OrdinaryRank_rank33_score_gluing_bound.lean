-- Prove2me | Theorems.Thm_Conway99Formal_OrdinaryRank_rank33_score_gluing_bound
-- name    : Conway99Formal.OrdinaryRank.rank33_score_gluing_bound
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T01:46:30.780089+00:00
-- url     : https://prove2.me/theorems/bd7efacc-561e-4101-af2c-9945130f5649
-- title:
--   Conditional determinant bound for rank-33 score-pair gluing
-- statement:
--   Let s and j be natural numbers, and let d and detC0 be rational numbers. Assume s≤2, j≤2^s, d≥0, and detC0·14^s=d·7^9·j². Then detC0≤(2/7)^s·d·7^9. In the source argument, s counts norm-14 score pairs and j is the gluing index in one score lattice, but this theorem assumes their bounds and determinant identity. It does not construct the score lattice or prove these premises for an SRG(99,14,1,2).
-- source:
--   UNIVERSAL_ORDINARY_RANK32.md §4 in archive/clean-start/proof-library.zip, SHA-256 3269235528f036976115c7c63aa24b06e16957b35cac703aa2a23881d2ef4761; conditional Lean theorem rank33_score_gluing_bound at lane commit 618028583f0a00cffa2acc0cc8ff1d57057acfe8. The actual score lattice, complete norm-14 shell, pairings, primitive span, gluing quotient, determinant identity and published packing inputs remain separate proof obligations. The public Conway target is unresolved.

import Definitions.Def_Conway99_OrdinaryRank_Rank33Gluing_20261004
set_option autoImplicit false

theorem Conway99Formal.OrdinaryRank.rank33_score_gluing_bound (s j : ℕ) (d detC0 : ℚ)
    (hs : s ≤ 2) (hj : j ≤ 2 ^ s) (hd : 0 ≤ d)
    (hdet : detC0 * 14 ^ s = d * 7 ^ 9 * (j : ℚ) ^ 2) :
    detC0 ≤ (2 / 7 : ℚ) ^ s * d * 7 ^ 9 := by sorry
