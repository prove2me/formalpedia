-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_claim_6_1
-- name    : BLTCounting.AccuracySpace.claim_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:12.866809+00:00
-- url     : https://prove2.me/theorems/72c4b025-38ab-4381-bc8b-20f374d954a7
-- title:
--   Spectral norm from row and column sums
-- statement:
--   For every complex matrix $B\in\mathbb C^{m\times n}$,
--   $$\|B\|_2^2\le\|B\|_1\|B\|_\infty,$$
--   where $\|B\|_1=\max_j\sum_i|B[i,j]|$ and $\|B\|_\infty=\max_i\sum_j|B[i,j]|$. This turns entrywise bounds into a spectral-norm bound.
--
--   Differences from the source:
--   - generalization: $B\in\mathbb C^{m\times n}$ with $m,n\ge1$ → any finite index types, including empty ones; reason: on an empty index type both sides are $0$; the source statement is the special case
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Claim 6.1, printed p. 34 (PDF p. 35)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_MatrixNorms

namespace BLTCounting.AccuracySpace

/-- Claim 6.1, PDF p. 35: `‖B‖₂² ≤ ‖B‖₁ ‖B‖_∞` for every complex matrix `B`, where `‖B‖₁` is the
maximum absolute column sum and `‖B‖_∞` the maximum absolute row sum. -/
theorem claim_6_1 {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (B : Matrix m n ℂ) :
    specNorm B ^ 2 ≤ maxColSum B * maxRowSum B := by sorry

end BLTCounting.AccuracySpace
