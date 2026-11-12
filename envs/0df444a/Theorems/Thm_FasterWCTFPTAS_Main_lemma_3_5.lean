-- Prove2me | Theorems.Thm_FasterWCTFPTAS_Main_lemma_3_5
-- name    : FasterWCTFPTAS.Main.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:56.256376+00:00
-- url     : https://prove2.me/theorems/e0541c4d-f681-4341-9527-baaeea2d879c
-- title:
--   Lemma 3.5 (Theorem 2.6 for m = 2 in [Cha06]) — planar ε-kernels of size O(1/√ε) in time O(N + 1/√ε)
-- statement:
--   There are an admissible program and a constant $C>0$ such that for every $N$, every list of $N$ points of $\mathbb R^2$ and every $\varepsilon\in(0,1)$, the program halts within
--
--   $$
--   C\Big(N+\frac1{\sqrt\varepsilon}\Big)
--   $$
--
--   steps and outputs the indices of at most $C/\sqrt\varepsilon$ input points that form an $\varepsilon$-kernel of the input points.
--
--   This is Chan's construction in the plane, cited by the paper; it avoids the extra $\alpha$ in the exponent and gives the $m=2$ clauses of Lemma 3.6, Corollary 4.7 and Theorem 1.1.
--
--   **Formalization Note** The program and $C$ are fixed before the input. The input is $[\varepsilon]$ followed by the coordinates of the points; the output is a list of indices into the input.
--
--   Differences from the source:
--   - reading: running time in O(·), machine model not named → number of executed instructions of an admissible program of the deterministic unit-cost real RAM of FasterWCTFPTAS.Main.Machine (rational literals, exact + − × ÷, comparisons, indirect addressing, work-bounded floor); reason: the source names no machine; this model supports the cited real-arithmetic constructions and excludes bit tricks that would trivialize the bound
--   - reading: O(·) bounds with a fixed constant → ∃ C > 0 chosen together with the program, before N, the points and ε; it may depend only on the fixed m and α; reason: standard meaning of O(·) for a fixed dimension and constant α
--   - reading: range of ε not stated → ε ∈ (0, 1); reason: the bound involves log(1/ε) > 0 and ε-kernels with ε ≥ 1 are trivial; Lemma 3.3 and Lemma 3.6 use ε < 1
--   - encoding: a set of N points → a list Fin N → ℝ^{m−1} × ℝ of N points (repetitions allowed), written as its coordinates; the output is a list of indices into it and the size is the list length; reason: a set of N distinct points is a list without repetitions; the list length bounds the number of selected points
--   - encoding: ε-kernel defined through max/min of inner products → IsKernel additionally requires Q nonempty when S is nonempty; reason: the width of the empty set is undefined in the source; the condition excludes only that case
-- source:
--   Karl Bringmann, Anita Dürr, Karol Węgrzycki, STOC 2027 submission #1072 (October 2026), p. 11 (PDF p. 12), Lemma 3.5 (Theorem 2.6 for m = 2 in [Cha06])

import Mathlib
import Definitions.Def_FasterWCTFPTAS_Main_Machine
import Definitions.Def_FasterWCTFPTAS_Main_Encoding

set_option autoImplicit false

namespace FasterWCTFPTAS.Main

/-- Lemma 3.5 (Theorem 2.6 for m = 2 in [Cha06]), p. 11 (PDF 12): there are an admissible program
and a constant `C > 0` such that, given `N` points of `ℝ²` and `ε ∈ (0, 1)`, the program outputs an
`ε`-kernel of the points, of size at most `C/√ε`, within `C (N + 1/√ε)` steps. -/
theorem lemma_3_5 :
    ∃ P : Machine.Program, Machine.Admissible P ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (pts : Fin N → Pt 2) (ε : ℝ), 0 < ε → ε < 1 →
        ∃ idx : List (Fin N),
          Machine.output P (kernelInput ε pts) = some (indexOutput idx) ∧
          Machine.HaltsWithin P (kernelInput ε pts) (C * ((N : ℝ) + 1 / Real.sqrt ε)) ∧
          (idx.length : ℝ) ≤ C * (1 / Real.sqrt ε) ∧
          IsKernel ε (idxSet pts idx) (Set.range pts) := by sorry

end FasterWCTFPTAS.Main
