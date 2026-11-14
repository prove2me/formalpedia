-- Prove2me | Theorems.Thm_BCFGJPSSV26_FL_alg_polytime
-- name    : BCFGJPSSV26.FL.alg_polytime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:40:20.63541+00:00
-- url     : https://prove2.me/theorems/c30a3818-4ce8-4f85-b4ea-2b5786a18279
-- title:
--   Theorem 1.4 (Part I) — the facility-location algorithm runs in polynomial time
-- statement:
--   This is the running-time half of Theorem 1.4 of Part I (arXiv:2610.18144): the algorithm for uncapacitated facility location with a uniform opening cost runs in polynomial time.
--
--   **Setting.** An instance $I$ consists of $n$ clients, $m$ facilities, a number $k$ and rational distances on the $n+m$ points; $f$ is a rational opening cost. For a list $S$ of facilities, $\mathrm{cost}(S)$ is the sum over the clients of the distance to the nearest facility of $S$.
--
--   The algorithm $\mathcal A(I,f)$ computes two candidates. The *trivial solution* $T$ lists, without repetitions, the nearest facility of every client (the least index on ties). The *greedy run* $G$ rescales the client–facility distances to $d(j,i)/t+1$, where $t=\min\big(d_{\min}/(10^5 n),\,f\big)$ and $d_{\min}$ is the least positive client–facility distance, and runs CompleteSolution of the log-adaptive greedy algorithm of Part I, Section 5 (with the exact openability tests, the bid $[\alpha-1.224\,d]^+$, $\delta=10^{-6}$ and the paper's $\varepsilon=\delta/10$), from the empty solution at the scaled opening cost $\hat f=1.9499\,(1-\delta)\,f/t$; $G$ lists the facilities it opens. The output is $G$ if $G$ is a nonempty list of distinct facilities with $\mathrm{cost}(G)+1.9499\,f\,|G|<\mathrm{cost}(T)+1.9499\,f\,|T|$, and $T$ otherwise.
--
--   **Statement.** The map
--
--   $$(I,f)\ \longmapsto\ \mathcal A(I,f)$$
--
--   is computable in polynomial time: some deterministic multitape Turing machine (binary alphabet, finitely many states) computes it within time and space bounded by polynomially bounded functions of the length of the encoded input. The input is encoded as the pair of the instance ($n$, $m$, $k$ in binary, then the table of distances, each a rational in lowest terms with numerator and denominator in binary) and of $f$ (a rational in binary); the output is the list of the indices of the facilities, in binary.
--
--   **Role.** Together with the guarantee $\mathrm{cost}(S)\le 1.9499\,(\mathrm{OPT}_f-f|S|)$ of the same algorithm, this gives Theorem 1.4.
--
--   **Formalization Note** The statement is about the total function: it holds for all instances and all rational $f$, with no validity or sign assumption (the algorithm is defined on every input, division by zero being $0$). Polynomial time is in the bit length of the input, so it accounts for the sizes of the rational distances and of $f$.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Theorem 1.4 (Theorem 4.3 in full). Lean source: `BCFGJPSSV26.FL.alg_polytime`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/FL/PolyTime.lean#L153-L156

module

public import Definitions.Def_BCFGJPSSV26_FL_Algorithm
public import Definitions.Def_BCFGJPSSV26_FL_PolyTimeCtx
public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxMain
public import Definitions.Def_BCFGJPSSV26_Combine_PolyTime
public import Definitions.Def_BCFGJPSSV26_FL_PolyTime

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.FL

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)
open Greedy Greedy.PT

namespace PT

end PT

theorem alg_polytime : ComputableInPolyTime (fun p : Instance × ℚ ↦ alg (toRaw p.1) p.2)
    (encPair encInstance encRat) encCenters := by sorry

end BCFGJPSSV26.FL
end
