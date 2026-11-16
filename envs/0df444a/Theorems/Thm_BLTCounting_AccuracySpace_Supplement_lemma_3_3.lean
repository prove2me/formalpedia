-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_Supplement_lemma_3_3
-- name    : BLTCounting.AccuracySpace.Supplement.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:59:30.93056+00:00
-- url     : https://prove2.me/theorems/ed862bf7-fea1-4819-a278-d12b448eac86
-- title:
--   Lemma 3.3 — Uniform relative lattice entry error
-- statement:
--   Fix $\gamma\in(0,1]$. There is $C_\gamma>0$ such that, for every integer $m\ge2$ and every $0\le i,j<K$ on the Section 3 lattice,
--   $$|\widetilde H_S[i,j]-c_0((i-j)h)|\le C_\gamma m^{-1+\gamma/2}c_0((i-j)h).$$
--   The same constant works for all sizes and both indices. This is the full relative entry estimate.
--
--   Differences from the source:
--   - encoding: relative O(m^(-1+γ/2)) uniform over i,j → one positive Cγ before m,i,j; reason: explicit quantifiers express the same uniform O bound
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Lemma 3.3, printed p. 14 (PDF p. 15)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_Supplement_Lattice

namespace BLTCounting.AccuracySpace.Supplement

/-- Lemma 3.3, PDF p.15: the relative O constant precedes m and both lattice indices. -/
theorem lemma_3_3 (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 2 ≤ m → ∀ i j : Fin (latticeK m γ),
      ‖normalizedHankel m γ i j -
        (c0 ((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * latticeH m γ) : ℂ)‖ ≤
      C * (m : ℝ) ^ (-1 + γ / 2) *
        c0 ((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * latticeH m γ) := by sorry

end BLTCounting.AccuracySpace.Supplement
