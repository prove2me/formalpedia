-- Prove2me | Theorems.Thm_DetPermanentApprox_Main_lemma_4_3
-- name    : DetPermanentApprox.Main.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:30:55.118509+00:00
-- url     : https://prove2.me/theorems/e66597e4-30fb-42b3-a3d4-11f3212b9505
-- title:
--   Lemma 4.3 — Numerical surrogate minimization with cost and bit bounds
-- statement:
--   Let $n\ge2$, let $C,p$ satisfy the rounded-data conditions, and let $s\ge2$ fix $t,\eta,K$ as in (4.1). The explicit numerical procedure has at least one recorded objective round and returns a rational $\widehat F$ satisfying
--
--   $$F_C(t)\le\widehat F\le F_C(t)+2\eta n.$$
--
--   One finite arithmetic program computes this particular recorded minimum, including construction of the actual $U$, in $n^{O(m)}\operatorname{poly}(p,m)$ operations. The output length and all rational intermediate lengths are polynomial in $n,p,m$, uniformly over the input. The trace bounds are on that same run. This retains the numerical accuracy, construction cost and bit clauses of Lemma 4.3 and its Appendix A implementation.
--
--   Differences from the source:
--   - encoding: finite labelled matrix, graph, and coordinate sets → Fin n or arbitrary finite types with explicit row and column copies; reason: finite enumerations and reindexing preserve every source instance
--   - encoding: arithmetic operations and comparisons with polynomial rational intermediate bit lengths → finite rational-literal real pointer programs, guarded divisions, explicit input/output layouts, and bounds on actual runs and traces; reason: each executed instruction has unit cost and no elementary-function or counting oracle is present; polynomial control overhead is absorbed in the source asymptotic bounds
--   - encoding: Algorithm 2 and the approximation procedures of Appendix A → the explicit Taylor approximation, first eligible vertex, nearest dyadic rounding with upward ties, and coordinatewise clipping; reason: these fix the permitted deterministic choices in the source procedure without assuming their accuracy
--   - encoding: C,U,t,eta,p,s supplied as above, and existence of an output with the stated bounds → C,p,s as input, U,t,eta computed by their defining formulas, and the exact recorded minimum; reason: the omitted input fields are uniquely determined by the supplied data; computing U is included in the execution cost
--   - encoding: output bit bound and the implementation analysis through p.30 → output and complete rational trace bounds, plus nonempty recorded rounds; reason: these are the explicit well-definedness and intermediate-size conclusions established in Appendix A and used in the main strong-polynomial claim
--   - generalization: C and p produced by Algorithm 1 preprocessing → any rational C and natural p satisfying RoundedData, with the same Section 4 parameters; reason: every source output satisfies RoundedData; the arguments on pp.21-30 use only its entry, grid, permanent and support properties, without the construction history or the least choice of p
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #704 (October 2026), Lemma 4.3, p. 22 (PDF p. 22); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/704.pdf

import Mathlib
import Definitions.Def_DetPermanentApprox_Main_Numerical
import Definitions.Def_DetPermanentApprox_Main_Analysis

namespace DetPermanentApprox.Main

theorem lemma_4_3 :
    ∃ P : Program, RationalProgram P ∧ ∃ c : ℝ, ∃ b d : ℕ, 0 < c ∧ 0 < b ∧
      ∀ (n : ℕ), 2 ≤ n → ∀ (C : Matrix (Fin n) (Fin n) ℚ) (p s : ℕ),
      2 ≤ s → RoundedData C p →
      (recordedRounds C p s).Nonempty ∧
      F (realMatrix C) (targetMarginal s : ℝ) ≤ (minimizedValue C p s : ℝ) ∧
      (minimizedValue C p s : ℝ) ≤ F (realMatrix C) (targetMarginal s : ℝ) + 2 * (eta s : ℝ) * n ∧
      rationalLength (minimizedValue C p s) ≤ b * (n + p + matrixDegree s + 1) ^ d ∧
      ∃ T : ℕ, validRun P (minimizationInput C p s) T ∧
        (T : ℝ) ≤ (n : ℝ) ^ (c * matrixDegree s) * (p + matrixDegree s + 1 : ℝ) ^ d ∧
        output P (minimizationInput C p s) T = (minimizedValue C p s : ℝ) ∧
        traceBound P (rationalMatrixInput C ++ [(p : ℚ), (s : ℚ)]) T
          (b * (n + p + matrixDegree s + 1) ^ d) := by sorry

end DetPermanentApprox.Main
