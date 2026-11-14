-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_core_polytime
-- name    : BCFGJPSSV26.Greedy.core_polytime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:43:03.661374+00:00
-- url     : https://prove2.me/theorems/9d810e3e-b397-4f04-bd01-cc041bb4b54f
-- title:
--   The core of the algorithm of Theorem 1.2 (greedy, bisection and merge) runs in polynomial time
-- statement:
--   This result states that, for fixed constants, the core of the algorithm of Theorem 1.2 of Part I is computable in polynomial time.
--
--   **The core.** Fix a triple $c=(\delta,\varepsilon,\varepsilon')$ of rational constants. A *core input* is $x=(n,m,k,\text{table})$, where the table lists the rational distances between $n$ clients and $m$ facilities (a list of rows of rationals). On $x$ the core computes, in exact rational arithmetic, the parameters $M=8n^2/\varepsilon'+1$, $\eta=\delta^2/(100n^2)$, $R=\lceil 1/\varepsilon^2\rceil\cdot\lceil\log_2\lceil 5nM\rceil\rceil+1$, $K=2(1+\varepsilon^2)^R$ and $L=m+4$, a grid of $2^{P_f}+1$ opening costs in $[\delta,4nM]$ and a grid of $2^{P_u}+1$ offsets in $[0,K]$, with $P_f=\lceil\log_2\lceil 4nM/\eta\rceil\rceil$ and $P_u=\lceil\log_2\lceil K/\eta\rceil\rceil$. For an opening cost it builds a greedy solution of $2R$ sequences, each obtained by $L$ rounds that add the first facility passing the exact openability test of the sequence's type, if there is one. It bisects on the grid of opening costs for a solution with exactly $k$ regular facilities and, if none is found, merges the solutions at two adjacent grid points in $2R$ phases (walking one sequence towards the other, removing extra facilities, and searching the offset of a new free copy on the grid). The output is the list of the facilities of the resulting solution, free copies replaced by their originals, without repetitions.
--
--   **Statement.** For every $c$, the function $\mathrm{core}_c$ from core inputs to lists of natural numbers is computable in polynomial time: there are polynomially bounded functions $t,s$ and a deterministic multitape Turing machine that, on the encoding $\langle x\rangle$ of any core input $x$, outputs the encoding of $\mathrm{core}_c(x)$ within
--
--   $$t(\lvert\langle x\rangle\rvert)\ \text{steps}\quad\text{and}\quad s(\lvert\langle x\rangle\rvert)\ \text{cells}.$$
--
--   No condition is put on $c$ or on $x$, and no correctness property of the core is used or asserted.
--
--   The main algorithm of Theorem 1.2 runs the core once for every guess of the scale of the distances, on the scaled instance; this result is the main part of the proof that the algorithm of Theorem 1.2 runs in polynomial time.
--
--   **Formalization Note** In the encoding of a core input, $n$ and $m$ are written in unary, $k$ in binary, and the table as a list of rows of rationals; the output is a list of numbers in binary. Unary $n$ and $m$ are needed because the core loops over all clients and facilities; for a k-median instance they are at most the length of its encoding, whose table has $n+m$ rows. The machine has a binary alphabet and finitely many states.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172). Lean source: `BCFGJPSSV26.Greedy.core_polytime`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/PolyTime/Core.lean#L53-L55

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Defs
public import Definitions.Def_BCFGJPSSV26_Basic_Raw
public import Definitions.Def_BuhaiPapers_Background_PolyTime_Rat
public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxCore
public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_Core

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Greedy

open Turing.MultiTapeTM

theorem core_polytime (c : Consts) : ComputableInPolyTime (core c) encCoreIn (encList encNat) := by sorry

end BCFGJPSSV26.Greedy
end
