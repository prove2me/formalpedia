-- Prove2me | Theorems.Thm_DenseMatching_IPM_theorem_1_1
-- name    : DenseMatching.IPM.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:40:53.240744+00:00
-- url     : https://prove2.me/theorems/b90e8236-64fa-465c-a493-23385a7674f1
-- title:
--   Theorem 1.1 — maximum bipartite matching size in Ö(n² log⁴ n) steps on a randomized pointer machine with failure probability ≤ n^{−c}
-- statement:
--   Maximum bipartite matching size can be computed in $\ddot O(n^2\log^4n)$ time on a pointer machine with high probability, where $\ddot O$ hides $(\log\log n)^{O(1)}$ factors. Precisely: for every constant $c\ge1$ there are a program $P$ of the randomized pointer machine of §2 (`PointerMachine`: words of $K\lceil\log_2\max(n,4)\rceil$ bits with $K$ fixed by the program; $+,-,\times$, integer division, remainder, comparison; pointer fields; uniform, Gaussian and Poisson draws at word precision) and a constant $C$ such that for every $n\ge1$ and every simple bipartite graph $G$ with given sides on $n$ vertices,
--   $$\Pr_{\omega}\Big[\text{the run of }P\text{ on }G\text{ halts within }C\,N^2(\log_2N)^4(\log_2\log_2N)^C\text{ steps, without a fault, with output }\nu(G)\Big]\ge1-n^{-c},\qquad N=\max(n,4).$$
--   The program and $C$ are fixed before the input; the input is the graph alone (no matching, no LP value), in the linked-list layout of `PointerMachine`, and any edge set (including unbalanced sides and no perfect matching) is allowed.
--
--   **Formalization Note.** The failure event is bounded in outer measure by `ENNReal.ofReal (n^(-c))` under the i.i.d. tape measure, which implies the success probability bound.
--
--   Differences from the source:
--   - reading: Ö(n² log⁴ n) time, Ö hiding (log log n)^{O(1)} (footnote 1) → at most timeBound C n = C·N²·(log₂ N)⁴·(log₂ log₂ N)^C steps, N = max(n, 4), one constant C for all n ≥ 1; reason: the standard meaning of Ö; N = max(n, 4) keeps log₂ log₂ N ≥ 1 for small n
--   - reading: 'with high probability' → ∀ c ≥ 1, ∃ program P and C: failure probability ≤ n^{−c} for every n ≥ 1; reason: the standard meaning; the proof (p. 51) reaches n^{−10} and any c by repetition with a majority vote
--   - reading: 'a pointer machine' (p. 7): O(log n)-bit words, +, −, ×, integer division, remainder, comparison; random primitives for uniform, Gaussian and Poisson samples 'with n^{−O(1)} error' → the PointerMachine definition: K⌈log₂ max(n,4)⌉-bit words (K chosen by the program), overflow and nil dereference are faults, draws with the exact laws of word-precision discretizations (uniform word, round(2^{⌊w/2⌋} g) clipped, Poisson(a/2^{⌊w/2⌋}) clipped); reason: the paper fixes the operations but not the encoding of draws; exact discretized laws are the reading of 'n^{−O(1)} error, the same order as the rounding error of integer division'
--   - encoding: 'a graph with n vertices', the output 'the size of a maximum bipartite matching' → BipartiteInput n (sides given, edge list without duplicates, any order) in the linked-list layout of initConfig; output word register 0 at halt equal to matchingNumber G; reason: input layout and output convention of the machine; every input order is covered because the statement quantifies over all edge lists
--   - encoding: the probability over the machine's random draws → tapeMeasure {ω | ¬ SucceedsWithin …} ≤ ENNReal.ofReal (n^(−c)), an outer-measure bound on the failure event under the i.i.d. tape; reason: equivalent for measurable events and never weaker otherwise
-- source:
--   Dai, Peng, Sleator, Stepin, Yang, Approaching Optimality for Dense Bipartite Matching, STOC 2027 submission (manuscript sha256 0bdeb447…), p. 1, Theorem 1.1 and footnote 1 (proof p. 51)

import Mathlib
import Definitions.Def_DenseMatching_IPM_Bipartite
import Definitions.Def_DenseMatching_IPM_PointerMachine

namespace DenseMatching.IPM

/-- Theorem 1.1 (p. 1; proved p. 51). For every constant `c ≥ 1` there are a program `P` of the
randomized pointer machine of §2 and a constant `C` such that, for every `n ≥ 1` and every bipartite
input graph `G` on `n` vertices, with probability at least `1 − n^{−c}` over the random tape the run
of `P` on `G` halts within `C · N² (log₂ N)⁴ (log₂ log₂ N)^C` steps, `N = max(n, 4)`, without a
fault, and outputs the maximum matching size `ν(G)`. -/
theorem theorem_1_1 :
    ∀ c : ℝ, 1 ≤ c → ∃ P : Program, ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ G : BipartiteInput n,
      tapeMeasure {ω | ¬ SucceedsWithin P G (timeBound C n) ω} ≤
        ENNReal.ofReal ((n : ℝ) ^ (-c)) := by sorry

end DenseMatching.IPM
