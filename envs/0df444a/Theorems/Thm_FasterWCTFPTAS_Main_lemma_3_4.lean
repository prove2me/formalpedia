-- Prove2me | Theorems.Thm_FasterWCTFPTAS_Main_lemma_3_4
-- name    : FasterWCTFPTAS.Main.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:00.067235+00:00
-- url     : https://prove2.me/theorems/c24d1e52-3e1c-4ddf-ba6f-8276b4640c5f
-- title:
--   Lemma 3.4 (Theorem 1.1 in [AdFM17]) — ε-kernels of size O(1/ε^{(m−1)/2}) in time O(N log(1/ε) + 1/ε^{(m−1)/2+α})
-- statement:
--   Fix a dimension $m\ge2$ and a constant $\alpha>0$. There are an admissible program and a constant $C>0$ such that for every $N$, every list of $N$ points of $\mathbb R^m$ and every $\varepsilon\in(0,1)$, the program halts within
--
--   $$
--   C\Big(N\big(1+\log_2\tfrac1\varepsilon\big)+\frac1{\varepsilon^{(m-1)/2+\alpha}}\Big)
--   $$
--
--   steps and outputs the indices of at most $C/\varepsilon^{(m-1)/2}$ input points that form an $\varepsilon$-kernel of the input points.
--
--   This is the near-optimal kernel construction of Arya, da Fonseca and Mount, cited by the paper; with Lemma 3.3 it yields Lemma 3.6.
--
--   **Formalization Note** The program and $C$ are fixed before the input and depend only on $m$ and $\alpha$. The input is $[\varepsilon]$ followed by the coordinates of the points; the output is a list of indices into the input.
--
--   Differences from the source:
--   - reading: running time in O(·), machine model not named → number of executed instructions of an admissible program of the deterministic unit-cost real RAM of FasterWCTFPTAS.Main.Machine (rational literals, exact + − × ÷, comparisons, indirect addressing, work-bounded floor); reason: the source names no machine; this model supports the cited real-arithmetic constructions and excludes bit tricks that would trivialize the bound
--   - reading: O(·) bounds with a fixed constant → ∃ C > 0 chosen together with the program, before N, the points and ε; it may depend only on the fixed m and α; reason: standard meaning of O(·) for a fixed dimension and constant α
--   - reading: log(1/ε) in the time bound → 1 + log₂(1/ε); reason: the O(·) bound is asymptotic as ε → 0; read literally, N·log(1/ε) tends to 0 as ε → 1 and falls below the N steps needed to read the input; logarithms are base 2 (p. 1)
--   - reading: range of ε not stated → ε ∈ (0, 1); reason: the bound involves log(1/ε) > 0 and ε-kernels with ε ≥ 1 are trivial; Lemma 3.3 and Lemma 3.6 use ε < 1
--   - encoding: a set of N points → a list Fin N → ℝ^{m−1} × ℝ of N points (repetitions allowed), written as its coordinates; the output is a list of indices into it and the size is the list length; reason: a set of N distinct points is a list without repetitions; the list length bounds the number of selected points
--   - encoding: ε-kernel defined through max/min of inner products → IsKernel additionally requires Q nonempty when S is nonempty; reason: the width of the empty set is undefined in the source; the condition excludes only that case
-- source:
--   Karl Bringmann, Anita Dürr, Karol Węgrzycki, STOC 2027 submission #1072 (October 2026), p. 11 (PDF p. 12), Lemma 3.4 (Theorem 1.1 in [AdFM17])

import Mathlib
import Definitions.Def_FasterWCTFPTAS_Main_Machine
import Definitions.Def_FasterWCTFPTAS_Main_Encoding

set_option autoImplicit false

namespace FasterWCTFPTAS.Main

/-- Lemma 3.4 (Theorem 1.1 in [AdFM17]), p. 11 (PDF 12): for every dimension `m ≥ 2` and every
constant `α > 0` there are an admissible program and a constant `C > 0` (depending only on `m` and
`α`) such that, given `N` points of `ℝ^m` and `ε ∈ (0, 1)`, the program outputs an `ε`-kernel of the
points, of size at most `C/ε^{(m−1)/2}`, within `C (N (1 + log₂(1/ε)) + 1/ε^{(m−1)/2+α})` steps. -/
theorem lemma_3_4 (m : ℕ) (hm : 2 ≤ m) (α : ℝ) (hα : 0 < α) :
    ∃ P : Machine.Program, Machine.Admissible P ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (pts : Fin N → Pt m) (ε : ℝ), 0 < ε → ε < 1 →
        ∃ idx : List (Fin N),
          Machine.output P (kernelInput ε pts) = some (indexOutput idx) ∧
          Machine.HaltsWithin P (kernelInput ε pts)
            (C * ((N : ℝ) * (1 + Real.logb 2 (1 / ε)) + (1 / ε) ^ (((m : ℝ) - 1) / 2 + α))) ∧
          (idx.length : ℝ) ≤ C * (1 / ε) ^ (((m : ℝ) - 1) / 2) ∧
          IsKernel ε (idxSet pts idx) (Set.range pts) := by sorry

end FasterWCTFPTAS.Main
