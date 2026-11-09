-- Prove2me | Theorems.Thm_DetPermanentApprox_Main_lemma_4_1
-- name    : DetPermanentApprox.Main.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:30:51.419162+00:00
-- url     : https://prove2.me/theorems/b73ec17d-19a9-4b98-ac3d-edeb2839b828
-- title:
--   Lemma 4.1 — Strongly polynomial scaling and rounding
-- statement:
--   Let $n\ge2$, let $A$ be a nonnegative real matrix with positive permanent, and let $\alpha=2^{-s}$ for an integer $s\ge1$. One deterministic arithmetic program returns $S>0$, $p\ge0$, and $C\in[0,1]^{n\times n}$ with exactly the support of $A$, such that
--
--   $$S\operatorname{per}A\le\operatorname{per}C\le(1+\alpha)S\operatorname{per}A,\qquad \operatorname{per}C\ge1.$$
--
--   Every entry of $C$ is a nonnegative integer multiple of $2^{-p}$. Uniformly over the input matrix, $p=O(n\log n+s)$ and the execution cost is polynomial in $n,s$. On rational input all intermediate rational bit lengths are polynomial in the input length and $s$, as specified in the proof on p.21. This prepares a bounded grid instance without a reduced-support promise on the input.
--
--   Differences from the source:
--   - encoding: finite labelled matrix, graph, and coordinate sets → Fin n or arbitrary finite types with explicit row and column copies; reason: finite enumerations and reindexing preserve every source instance
--   - encoding: permanent summed over row-to-column permutations → Mathlib matrix permanent with the inverse permutation convention; reason: reindexing the finite sum by permutation inversion gives exactly the source value
--   - encoding: arithmetic operations and comparisons with polynomial rational intermediate bit lengths → finite rational-literal real pointer programs, guarded divisions, explicit input/output layouts, and bounds on actual runs and traces; reason: each executed instruction has unit cost and no elementary-function or counting oracle is present; polynomial control overhead is absorbed in the source asymptotic bounds
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #704 (October 2026), Lemma 4.1, p. 20 (PDF p. 20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/704.pdf

import Mathlib
import Definitions.Def_DetPermanentApprox_Main_Numerical
import Definitions.Def_DetPermanentApprox_Main_Analysis

namespace DetPermanentApprox.Main

theorem lemma_4_1 :
    ∃ P : Program, RationalProgram P ∧
    ∃ c : ℝ, ∃ b d a e : ℕ, 0 < c ∧ 0 < b ∧ 0 < a ∧
    (∀ (n : ℕ), 2 ≤ n → ∀ A : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, 0 ≤ A i j) → 0 < A.permanent → ∀ s : ℕ, 1 ≤ s →
      ∃ (T p : ℕ) (S : ℝ) (C : Matrix (Fin n) (Fin n) ℝ),
        validRun P (scaleInput A s) T ∧ T ≤ b * (n + s + 1) ^ d ∧
        output P (scaleInput A s) T = S ∧
        (run P (scaleInput A s) T).mem 0 = (p : ℝ) ∧
        (∀ i j : Fin n, (run P (scaleInput A s) T).mem (1 + (i : ℤ) * n + (j : ℤ)) = C i j) ∧
        0 < S ∧ (∀ i j, 0 ≤ C i j ∧ C i j ≤ 1) ∧
        (∀ i j, 0 < C i j ↔ 0 < A i j) ∧
        S * A.permanent ≤ C.permanent ∧ C.permanent ≤ (1 + (alpha s : ℝ)) * S * A.permanent ∧
        1 ≤ C.permanent ∧ (∀ i j, ∃ k : ℕ, C i j = k / (2 : ℝ) ^ p) ∧
        (p : ℝ) ≤ c * ((n : ℝ) * Real.log n + s)) ∧
    (∀ (n : ℕ), 2 ≤ n → ∀ A : Matrix (Fin n) (Fin n) ℚ,
      (∀ i j, 0 ≤ A i j) → 0 < (realMatrix A).permanent → ∀ s : ℕ, 1 ≤ s →
      ∃ T : ℕ, validRun P (scaleInput (realMatrix A) s) T ∧
        traceBound P (rationalScaleInput A s) T
          (a * (inputLength (rationalScaleInput A s) + s + 1) ^ e)) := by sorry

end DetPermanentApprox.Main
