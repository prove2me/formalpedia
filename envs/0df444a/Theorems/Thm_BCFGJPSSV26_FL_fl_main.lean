-- Prove2me | Theorems.Thm_BCFGJPSSV26_FL_fl_main
-- name    : BCFGJPSSV26.FL.fl_main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:41:31.172708+00:00
-- url     : https://prove2.me/theorems/667b91d9-8921-4273-b1bb-43f98df24c88
-- title:
--   Theorem 1.4 (Part I) — the facility-location LMP theorem, as proved in the development
-- statement:
--   This is Theorem 1.4 of Part I (arXiv:2610.18144; Theorem 4.3 in the full version): there is a polynomial-time $1.9499$-LMP approximation algorithm for uncapacitated facility location with a uniform opening cost.
--
--   **Setting.** A valid instance $I$ has $n$ clients, $m\ge 1$ facilities and rational distances forming a pseudometric on the $n+m$ points (and a number $k\ge1$, which plays no role). For a nonempty set $S$ of facilities, $\mathrm{cost}(S)=\sum_j\min_{i\in S}d(j,i)$ over the clients $j$, and for an opening cost $f$,
--
--   $$\mathrm{OPT}_f=\min_{S'\ne\emptyset}\big(\mathrm{cost}(S')+f\,|S'|\big).$$
--
--   **Statement.** There is a deterministic algorithm $A$, taking an instance and a rational number and returning a list of natural numbers, such that:
--
--   1. $A$ is computable in polynomial time: a multitape Turing machine computes it within time and space polynomially bounded in the length of the encoded input $(I,f)$ (the instance as $n$, $m$, $k$ in binary and its table of distances, $f$ as a rational in binary);
--   2. for every valid instance $I$ with at least one client and every rational $f\ge0$, the output $S=A(I,f)$ is a nonempty list of distinct facilities of $I$ with
--
--   $$\mathrm{cost}(S)\ \le\ 1.9499\,\big(\mathrm{OPT}_f-f\,|S|\big).$$
--
--   **Role.** This is the statement of the main theorem on facility location, proved inside the development; the main theorem is this result verbatim. The witness is the explicit algorithm that outputs the better of one run of the log-adaptive greedy algorithm on a rescaled instance and the trivial solution (the nearest facility of every client); item 1 is its polynomial running time and item 2 its guarantee.
--
--   **Formalization Note** The paper's Theorem 4.3 says that Algorithm 1 with the bid $[\alpha-1.224\,d]^+$ and the opening cost $1.9499f$ is such an algorithm; the formal statement asserts that some algorithm has the guarantee. Instances without clients are excluded because outputs and $\mathrm{OPT}_f$ range over nonempty sets.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Theorem 1.4 (Theorem 4.3 in full). Lean source: `BCFGJPSSV26.FL.fl_main`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/FL/Main.lean#L76-L78

module

public import Definitions.Def_BCFGJPSSV26_FL_Run
public import Definitions.Def_BCFGJPSSV26_FL_PolyTime
public import Definitions.Def_BCFGJPSSV26_FL_Main

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.FL

open Encoding

variable {I : Instance}

theorem fl_main : Thm14 := by sorry

end BCFGJPSSV26.FL
end
