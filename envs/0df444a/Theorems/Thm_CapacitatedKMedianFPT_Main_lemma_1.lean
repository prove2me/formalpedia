-- Prove2me | Theorems.Thm_CapacitatedKMedianFPT_Main_lemma_1
-- name    : CapacitatedKMedianFPT.Main.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:15:32.582815+00:00
-- url     : https://prove2.me/theorems/dd8f41fc-da17-4f60-a471-d8224e080d02
-- title:
--   Lemma 1 — pre-processing to integral distances in [1, ⌈3αn²/ε⌉]
-- statement:
--   Let $0<\varepsilon<1$ and $\alpha\ge1$. Suppose there is a deterministic $\alpha$-approximation algorithm with running time $T(n,k)$ for every capacitated $k$-median instance on $n$ points whose distances (between distinct points) are positive integers in the range
--   $$\Bigl[1,\Bigl\lceil\frac{3\alpha n^2}{\varepsilon}\Bigr\rceil\Bigr].$$
--   Then there is a deterministic $\alpha(1+\varepsilon)$-approximation algorithm with running time $T(n,k)\cdot n^2+n^{O(1)}$ for every capacitated $k$-median instance on $n$ points.
--
--   Here $n=|C|+|F|$ and instances are feasible. The lemma lets the rest of the paper assume integral distances bounded polynomially in $n$; the reduction runs the given algorithm once for each of the $O(n^2)$ candidate values of the largest optimal assignment distance.
--
--   **Formalization Note** Both algorithms are programs of `Machine` whose time is measured on the word RAM with the word length of their own input (`wordSizeOf`). The conclusion bounds the time by $c\cdot(T(n,k)\cdot n^2+n^e)$ with an absolute exponent $e$ chosen before $\varepsilon,\alpha$ and a constant $c$ that may depend on $\varepsilon,\alpha$ only (it is chosen before $T$ and the given algorithm).
--
--   Differences from the source:
--
--   - reading: running time T(n, k) and T(n, k)·n² + n^O(1), machine model unspecified → word-RAM time (`Stats.wordTime`) with the word length of the input (`wordSizeOf`) for both algorithms; reason: an overhead n^O(1) independent of the bit length of arbitrary distances is meaningful only when input numbers fit in a word; bit cost forces a dependence on |I|, and unit cost on unbounded rationals is a degenerate model
--   - reading: runtime T(n, k)·n² + n^O(1) → time ≤ c·(T(n, k)·n² + n^e), e absolute, c depending only on ε and α (chosen before T and the given algorithm); reason: running times are stated up to constant factors; a factor exactly 1 on T(n, k)·n² is not attainable when the given program must be run as a subroutine with relocated memory, and ε, α are the lemma's fixed parameters; the printed overhead does not depend on the given algorithm, so neither does c
--   - encoding: an instance I with input length |I| → a rational instance in the standard encoding (`RatInstance.encode`), |I| its total bit length; reason: an input length presupposes a finite exact representation; binary rationals are the standard one, and any rational instance is an instance of the source
--   - encoding: the sum of the k largest capacities is at least |C| → some k facilities have total capacity at least |C|; reason: equivalent conditions
--   - encoding: cost at most ρ·OPT → cost at most ρ times the cost of every solution; reason: OPT is the minimum over the finitely many assignments of C, so the two are equivalent
--   - encoding: outputs (S, φ) → S and φ read from fixed memory cells (`RatInstance.IsSolutionOutput`), the k facilities distinct; reason: the source does not fix an output format
--   - encoding: instance on n points → n = |C| + |F|; reason: the size notation of §2, p. 5
-- source:
--   Aditya Anand, Yichen Huang, Ragesh Jaiswal, Amit Kumar, Euiwoong Lee, Jatin Yadav, A Tight FPT Approximation for Capacitated k-Median, STOC 2027 submission #1646 (October 2026), p. 6, Lemma 1 (Pre-processing); proof p. 22, Appendix A

import Mathlib
import Definitions.Def_CapacitatedKMedianFPT_Main_Instance
import Definitions.Def_CapacitatedKMedianFPT_Main_Machine
import Definitions.Def_CapacitatedKMedianFPT_Main_Encoding

set_option autoImplicit false

namespace CapacitatedKMedianFPT.Main

/-- **Lemma 1 (Pre-processing)** (p. 6, proof p. 22). Running times are measured on the word RAM
whose word length is that of the input (`wordSizeOf`), and `n = |C| + |F|`. If a program `A` is a
deterministic `α`-approximation running within `T(n, k)` on every feasible instance whose distances
between distinct points are integers in `[1, ⌈3αn²/ε⌉]`, then some program `B` is a deterministic
`α(1+ε)`-approximation on every feasible instance, running within `c · (T(n, k) · n² + n^e)`; the
exponent `e` is absolute and the constant `c` depends only on `ε, α` (chosen before `T` and `A`, so
the overhead of the reduction does not depend on the given algorithm). -/
theorem lemma_1 :
    ∃ e : ℕ, ∀ (ε α : ℝ), 0 < ε → ε < 1 → 1 ≤ α → ∃ c : ℕ, ∀ T : ℕ → ℕ → ℕ,
      (∃ A : Program, ∀ I : RatInstance, I.toInstance.IsValid → I.toInstance.Feasible →
        I.toInstance.HasIntDistancesUpTo ⌈3 * α * (I.toInstance.size : ℝ) ^ 2 / ε⌉₊ →
        ∃ (mem : Memory) (s : Stats), RunsTo A zeroOracle I.encode mem s ∧
          s.wordTime (wordSizeOf I.encode) ≤ T I.toInstance.size I.k ∧
          I.IsSolutionOutput α mem) →
      ∃ B : Program, ∀ I : RatInstance, I.toInstance.IsValid → I.toInstance.Feasible →
        ∃ (mem : Memory) (s : Stats), RunsTo B zeroOracle I.encode mem s ∧
          s.wordTime (wordSizeOf I.encode) ≤
            c * (T I.toInstance.size I.k * I.toInstance.size ^ 2 + I.toInstance.size ^ e) ∧
          I.IsSolutionOutput (α * (1 + ε)) mem := by sorry

end CapacitatedKMedianFPT.Main
