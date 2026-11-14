-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_exists_algN_inO
-- name    : BCFGJPSSV26.Stable.exists_algN_inO
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:52:30.356386+00:00
-- url     : https://prove2.me/theorems/6a2c9545-612b-47b8-a8f6-81556cba45c2
-- title:
--   Running time of the stable-instance algorithm with $N$ given in unary
-- statement:
--   This is the running-time bound for the algorithm for stable instances of Part II when the accuracy parameter $N$ is part of the input, in unary: one machine and one exponent constant serve every $N$.
--
--   For an instance $I$ with encoding of length $|I|$, a natural number $L$ and $e\in\mathbb N$, put $\tau_e(I,L)=2^{eL}(|I|+2)^{e}$, and let $e_1(N)=10^6N^2$. The algorithm $\mathcal A$ takes an instance $I$ (in binary), natural numbers $L$ and $N$ (in unary) and a string $r$ of coin flips. With $s=632NL$, the budget $B=\tau_{e_1(N)}(I,L)$, $R=N^{200s+1}$ trials, $26s+20+k$ chunks per trial and chunks of $|I|+7N$ coins, it uses the first $R\,(26s+20+k)\,(|I|+7N)$ coins of $r$ and does the following, cutting every loop and enumeration at $B$: it runs the local search with swaps of at most $24N$ facilities; it runs $\min(R,B)$ trials, each on its own block of chunks (client sampling, cluster sampling, coloring and the submodular step, producing candidates); it turns the local-search solution and every candidate into a list of exactly $k$ distinct facilities and outputs the cheapest by exact cost.
--
--   **Statement.** There is a natural number $d$ such that $\mathcal A$ is computed by a deterministic multitape Turing machine that, for a constant $c$ and every input $(I,L,N,r)$, halts within
--
--   $$c\,\bigl(\tau_{\,d\,e_1(N)+d}(I,L)+|\mathrm{enc}(I,L,N,r)|+1\bigr)$$
--
--   steps, uses at most that many tape cells, and writes an output (a list of facility indices in binary) of at most that length.
--
--   The statement holds for all inputs, valid or not. It is combined with the computation of $N=N(\varepsilon)\le256(\lceil1/\varepsilon\rceil+1)$ from the rational accuracy $\varepsilon$ to obtain the running time $O\bigl(2^{eL}(|I|+2)^{e}\bigr)$, $e=a(\lceil1/\varepsilon\rceil+1)^2$, plus the length of the input, of the algorithm of Theorem 1.1 of Part II. The point is that $d$ and the machine do not depend on $N$: every polynomial-time step of the algorithm receives $N$, $L$ and $B$ in unary.
--
--   **Formalization Note** Time is counted on multitape Turing machines over the encoded input; the instance is encoded by $n$, $m$, $k$ in binary and its table of rational distances.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172). Lean source: `BCFGJPSSV26.Stable.exists_algN_inO`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Time/RunTime.lean#L309-L428

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

theorem exists_algN_inO : ∃ d : ℕ, ComputableInO algN encILNr encCenters
    (fun xr ↦ stableTime (d * Par.e₁ xr.1.2 + d) xr.1.1 + (encILNr xr).length)
    (fun xr ↦ stableTime (d * Par.e₁ xr.1.2 + d) xr.1.1 + (encILNr xr).length) := by sorry

end BCFGJPSSV26.Stable
end
