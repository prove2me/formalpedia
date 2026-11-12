-- Prove2me | Theorems.Thm_FasterWCTFPTAS_Main_lemma_3_6
-- name    : FasterWCTFPTAS.Main.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:15.266514+00:00
-- url     : https://prove2.me/theorems/00e0fe33-cc21-4e66-b7e6-2b1843c19f0c
-- title:
--   Lemma 3.6 — relaxed δ-representative sets of size O(1/δ^{(m−1)/2}) in time O(|D| log(1/δ) + 1/δ^{(m−1)/2+α}); for m = 2 size O(1/√δ) in time O(|D| + 1/√δ)
-- statement:
--   Fix a dimension $m\ge2$.
--
--   1. For every constant $\alpha>0$ there are an admissible program and a constant $C>0$ such that, given $\delta\in(0,1)$, $A,B,X\ge0$ and a list of $N$ pairs $D\subseteq[0,A]^{m-1}\times[0,B]$, the program halts within
--   $$
--   C\Big(N\big(1+\log_2\tfrac1\delta\big)+\frac1{\delta^{(m-1)/2+\alpha}}\Big)
--   $$
--   steps and outputs the indices of at most $C/\delta^{(m-1)/2}$ pairs of $D$ forming a relaxed $\delta$-representative set of $D$ for $(A,B,X)$.
--   2. If $m=2$, there are an admissible program and a constant $C>0$ doing the same with at most $C/\sqrt\delta$ output pairs within $C(N+1/\sqrt\delta)$ steps.
--
--   This is the algorithmic form of Lemma 3.3 and the source of the running time of Corollary 4.7.
--
--   **Formalization Note** Each program and its constant are fixed before the input and depend only on $m$ (and $\alpha$ in part 1). The input is $[\delta,A,B,X]$ followed by the coordinates of the pairs; the output is a list of indices into the input.
--
--   Differences from the source:
--   - reading: running time in O(·), machine model not named → number of executed instructions of an admissible program of the deterministic unit-cost real RAM of FasterWCTFPTAS.Main.Machine (rational literals, exact + − × ÷, comparisons, indirect addressing, work-bounded floor); reason: the source names no machine; this model supports the cited real-arithmetic constructions and excludes bit tricks that would trivialize the bound
--   - reading: O(·) bounds with a fixed constant → ∃ C > 0 chosen together with the program, before δ, A, B, X and D; it may depend only on the fixed m and α; reason: standard meaning of O(·) for a fixed dimension and constant α
--   - reading: log(1/δ) in the time bound → 1 + log₂(1/δ); reason: the O(·) bound is asymptotic as δ → 0; read literally, N·log(1/δ) tends to 0 as δ → 1 and falls below the N steps needed to read the input; logarithms are base 2 (p. 1)
--   - encoding: a set of N pairs → a list Fin N → ℝ^{m−1} × ℝ of N pairs (repetitions allowed), written as its coordinates; the output is a list of indices into it and the size is the list length; reason: a set of N distinct points is a list without repetitions; the list length bounds the number of selected points
-- source:
--   Karl Bringmann, Anita Dürr, Karol Węgrzycki, STOC 2027 submission #1072 (October 2026), p. 11 (PDF p. 12), Lemma 3.6

import Mathlib
import Definitions.Def_FasterWCTFPTAS_Main_Machine
import Definitions.Def_FasterWCTFPTAS_Main_Encoding

set_option autoImplicit false

namespace FasterWCTFPTAS.Main

/-- Lemma 3.6, p. 11 (PDF 12). Fix `m ≥ 2`.
(1) For every constant `α > 0` there are an admissible program and `C > 0` such that, given
`δ ∈ (0, 1)`, `A, B, X ≥ 0` and `N` pairs `D ⊆ [0, A]^{m−1} × [0, B]`, the program outputs a relaxed
`δ`-representative set of `D` for `(A, B, X)` of size at most `C/δ^{(m−1)/2}` within
`C (N (1 + log₂(1/δ)) + 1/δ^{(m−1)/2+α})` steps.
(2) If `m = 2`, there are an admissible program and `C > 0` doing the same with size at most `C/√δ`
within `C (N + 1/√δ)` steps. -/
theorem lemma_3_6 (m : ℕ) (hm : 2 ≤ m) :
    (∀ α : ℝ, 0 < α →
      ∃ P : Machine.Program, Machine.Admissible P ∧ ∃ C : ℝ, 0 < C ∧
        ∀ (δ A B X : ℝ), 0 < δ → δ < 1 → 0 ≤ A → 0 ≤ B → 0 ≤ X →
        ∀ (N : ℕ) (pts : Fin N → Pt m), (∀ j, InBox A B (pts j)) →
          ∃ idx : List (Fin N),
            Machine.output P (repInput δ A B X pts) = some (indexOutput idx) ∧
            Machine.HaltsWithin P (repInput δ A B X pts)
              (C * ((N : ℝ) * (1 + Real.logb 2 (1 / δ)) + (1 / δ) ^ (((m : ℝ) - 1) / 2 + α))) ∧
            (idx.length : ℝ) ≤ C * (1 / δ) ^ (((m : ℝ) - 1) / 2) ∧
            IsRelaxedRep δ A B X (idxSet pts idx) (Set.range pts)) ∧
    (m = 2 →
      ∃ P : Machine.Program, Machine.Admissible P ∧ ∃ C : ℝ, 0 < C ∧
        ∀ (δ A B X : ℝ), 0 < δ → δ < 1 → 0 ≤ A → 0 ≤ B → 0 ≤ X →
        ∀ (N : ℕ) (pts : Fin N → Pt m), (∀ j, InBox A B (pts j)) →
          ∃ idx : List (Fin N),
            Machine.output P (repInput δ A B X pts) = some (indexOutput idx) ∧
            Machine.HaltsWithin P (repInput δ A B X pts) (C * ((N : ℝ) + 1 / Real.sqrt δ)) ∧
            (idx.length : ℝ) ≤ C * (1 / Real.sqrt δ) ∧
            IsRelaxedRep δ A B X (idxSet pts idx) (Set.range pts)) := by sorry

end FasterWCTFPTAS.Main
