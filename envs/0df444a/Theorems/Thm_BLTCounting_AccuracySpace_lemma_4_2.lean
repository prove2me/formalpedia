-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_lemma_4_2
-- name    : BLTCounting.AccuracySpace.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:08.548614+00:00
-- url     : https://prove2.me/theorems/453a12ff-a6ab-485f-a182-90b10a01edde
-- title:
--   Weighted positivity and rank threshold
-- statement:
--   Let $c$ be a BLT sequence of recurrence order $d$, let $f$ be the square-root sequence, let $\eta>0$ with $\|f-c\|_{\ell_2(0,n-1)}\le\eta$, and put $m=\lfloor(n+1)/2\rfloor$. For every nonempty $S\subseteq\{1,\dots,m-1\}$:
--
--   1. $\widehat H_S(f)$ is positive definite;
--   2. $\|\widehat H_S(f)-\widehat H_S(c)\|_2=\|\widehat H_S(f-c)\|_2\le2\eta$;
--   3. $d\ge\#\{j:\lambda_j(\widehat H_S(f))>2\eta\}$.
--
--   This is the first spectral form of the lower bound: every eigenvalue of the weighted matrix above $2\eta$ costs one unit of recurrence order.
--
--   Differences from the source:
--   - generalization: the conditions of Theorem 1.2, including $n\ge n_0$ and $a_*\le\log(1/\eta)\le(1/2-\varepsilon)\log m$ → only $\eta>0$, the BLT recurrence and the error bound, for every $n$; reason: the conclusion uses no other part of those conditions, including $m\ge4$; the source statement is the special case
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Lemma 4.2, printed p. 25 (PDF p. 26)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_MatrixNorms
import Definitions.Def_BLTCounting_AccuracySpace_Sequences

open Matrix
open scoped ComplexOrder

namespace BLTCounting.AccuracySpace

/-- Lemma 4.2, PDF p. 26: let `c` be a BLT sequence of order at most `d` with
`‖f - c‖_{ℓ₂(0,n-1)} ≤ η`, `m = ⌊(n+1)/2⌋` and `∅ ≠ S ⊆ {1, …, m-1}`. Then `Ĥ_S(f)` is positive
definite, `‖Ĥ_S(f) - Ĥ_S(c)‖₂ = ‖Ĥ_S(f - c)‖₂ ≤ 2η`, and `d ≥ #{j : λ_j(Ĥ_S(f)) > 2η}`. -/
theorem lemma_4_2 (n d : ℕ) (c : ℕ → ℂ) (η : ℝ) (hη : 0 < η) (hc : IsBLT d c)
    (herr : coeffErr n sqrtSeq c ≤ η) (S : Finset ℕ) (hSne : S.Nonempty)
    (hS : S ⊆ Finset.Ico 1 ((n + 1) / 2)) :
    ∃ hP : (weightedHankel S sqrtSeq).PosDef,
      specNorm (weightedHankel S sqrtSeq - weightedHankel S c) =
          specNorm (weightedHankel S (sqrtSeq - c)) ∧
        specNorm (weightedHankel S (sqrtSeq - c)) ≤ 2 * η ∧
        eigCountAbove hP.isHermitian (2 * η) ≤ d := by sorry

end BLTCounting.AccuracySpace
