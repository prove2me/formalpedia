-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_Supplement_lemma_3_4
-- name    : BLTCounting.AccuracySpace.Supplement.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:00:01.384008+00:00
-- url     : https://prove2.me/theorems/1366bbec-93a5-453e-8cf7-e529ea3fdf08
-- title:
--   Lemma 3.4 — Uniform operator-norm approximation
-- statement:
--   For every fixed $\gamma\in(0,1]$ there is $C_\gamma>0$ such that, for every integer $m\ge2$,
--   $$\|\widetilde H_S-T_h\|_2\le C_\gamma/(\log m).$$
--   Here the matrices are the actual Section 3 lattice matrices and the norm is the complex Euclidean operator norm. The assertion includes every $m\ge2$, rather than only an eventual bound.
--
--   Differences from the source: none.
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Lemma 3.4, printed p. 15 (PDF p. 16)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_Supplement_Lattice

namespace BLTCounting.AccuracySpace.Supplement

/-- Lemma 3.4, PDF p.16: all m ≥ 2, with C depending only on γ. -/
theorem lemma_3_4 (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 2 ≤ m →
      specNorm (normalizedHankel m γ - latticeToeplitz m γ) ≤ C / latticeL m := by sorry

end BLTCounting.AccuracySpace.Supplement
