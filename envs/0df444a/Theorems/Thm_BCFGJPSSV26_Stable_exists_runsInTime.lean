-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_exists_runsInTime
-- name    : BCFGJPSSV26.Stable.exists_runsInTime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:52:41.833615+00:00
-- url     : https://prove2.me/theorems/68e61a91-713e-4251-896c-522bfe50a647
-- title:
--   Running time of the algorithm of Theorem 1.1 (Part II): $O(2^{eL}(|I|+2)^e)$, $e=a(\lceil 1/\varepsilon\rceil+1)^2$
-- statement:
--   This is the running-time part of Theorem 1.1 of Part II: the algorithm for stable instances, with the accuracy $\varepsilon$ as an input, runs in time $O\bigl(2^{eL}(|I|+2)^{e}\bigr)$ with $e=a(\lceil1/\varepsilon\rceil+1)^2$, plus the length of its input, for an absolute constant $a$.
--
--   For an instance $I$ with encoding of length $|I|$, a natural number $L$ and a rational number $\varepsilon$, put
--
--   $$T_a(I,L,\varepsilon)=2^{eL}\,(|I|+2)^{e},\qquad e=a\,(\lceil1/\varepsilon\rceil+1)^{2}.$$
--
--   The algorithm $\mathcal A_{\mathbb Q}$ takes $I$ (in binary), $L$ (in unary), $\varepsilon=p/q$ (in binary) and a string $r$ of coin flips. It computes $N=N(\varepsilon)=2^{g+8}$, where $g=\max(0,\mathrm{size}(q)-\mathrm{size}(p)-1)$ for $p\ge0$ and $g=0$ for $p<0$, with $\mathrm{size}$ the number of binary digits, and runs the algorithm for accuracy $1/N$: local search with swaps of at most $24N$ facilities, then up to $N^{200s+1}$ trials of the samplings and the submodular step, $s=632NL$, with every loop cut at the budget $B(N,I,L)=2^{e_1L}(|I|+2)^{e_1}$, $e_1=10^6N^2$; the output is the cheapest candidate, as a list of facilities.
--
--   **Statement.** There is a natural number $a$ such that:
--
--   1. $\mathcal A_{\mathbb Q}$ is computed by a deterministic multitape Turing machine that, for a constant $c$ and every input, halts within
--   $$c\,\bigl(T_a(I,L,\varepsilon)+|\mathrm{enc}(I,L,\varepsilon,r)|+1\bigr)$$
--   steps and uses at most that many tape cells;
--   2. for every $I$, $L$ and $\varepsilon$, the budget satisfies $B(N(\varepsilon),I,L)\le T_a(I,L,\varepsilon)$.
--
--   Part 1 is the running-time clause of the main theorem, with exponent $b=2$. Part 2 is used for its probability clause: the algorithm reads at most $B$ coins when $k\le m$, so a uniformly random string of $T_a(I,L,\varepsilon)$ coins contains all the coins the algorithm reads, and the success probability computed over those coins transfers.
--
--   **Formalization Note** The statement holds for all inputs, including invalid instances and $\varepsilon\le0$, where $\lceil1/\varepsilon\rceil$ is $0$ as a natural number. The proof gives $a=d'(10^6\cdot2^{16}+1)$, where $d'$ bounds the degrees of the polynomial-time certificates of the steps.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Theorem 1.1 (running time). Lean source: `BCFGJPSSV26.Stable.exists_runsInTime`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Time/RunTime.lean#L465-L504

module

public import Definitions.Def_BCFGJPSSV26_Stable_Time_PolyTimeCore
public import Definitions.Def_BCFGJPSSV26_Stable_Time_Accuracy
public import Definitions.Def_BuhaiPapers_Background_BlackBox
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_Constructible
public import Definitions.Def_BCFGJPSSV26_Stable_Time_RunTime

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

theorem exists_runsInTime : ∃ a : ℕ, RunsInTime encILQ encCenters algQ (stableTimeOf a 2) ∧
    ∀ x : (Instance × ℕ) × ℚ, Par.budget (accN x.2) x.1.1 x.1.2 ≤ stableTimeOf a 2 x := by sorry

end BCFGJPSSV26.Stable
end
