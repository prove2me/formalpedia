-- Prove2me | Theorems.Thm_BCFGJPSSV26_FL_alg_spec
-- name    : BCFGJPSSV26.FL.alg_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:39:52.555257+00:00
-- url     : https://prove2.me/theorems/6e8dc608-ef34-47c8-9c12-13e39e20f0a9
-- title:
--   Theorem 1.4 (Part I) — the LMP guarantee of the facility-location algorithm
-- statement:
--   This is the guarantee of the algorithm behind Theorem 1.4 of Part I (arXiv:2610.18144; Theorem 4.3 in the full version): its output satisfies the $1.9499$-LMP bound for uncapacitated facility location with a uniform opening cost.
--
--   **Setting.** Let $I$ be a valid instance: $n$ clients, $m\ge1$ facilities and rational distances forming a pseudometric on the $n+m$ points (and a number $k\ge 1$, which plays no role). Assume $n\ge 1$, and let $f\ge 0$ be a rational opening cost. For a nonempty set $S$ of facilities, $\mathrm{cost}(S)=\sum_j\min_{i\in S}d(j,i)$ over the clients $j$, and
--
--   $$\mathrm{OPT}_f=\min_{S'\ne\emptyset}\big(\mathrm{cost}(S')+f\,|S'|\big).$$
--
--   The algorithm $\mathcal A(I,f)$ computes two candidates. The *trivial solution* $T$ lists, without repetitions, the nearest facility of every client (the least index on ties). The *greedy run* $G$ rescales the client–facility distances to $d(j,i)/t+1$, where $t=\min\big(d_{\min}/(10^5 n),\,f\big)$ and $d_{\min}$ is the least positive client–facility distance, and runs CompleteSolution of the log-adaptive greedy algorithm of Part I, Section 5 (with the exact openability tests, the bid $[\alpha-1.224\,d]^+$, $\delta=10^{-6}$ and the paper's $\varepsilon=\delta/10$), from the empty solution at the scaled opening cost $\hat f=1.9499\,(1-\delta)\,f/t$; $G$ lists the facilities it opens. The output is $G$ if $G$ is a nonempty list of distinct facilities with $\mathrm{cost}(G)+1.9499\,f\,|G|<\mathrm{cost}(T)+1.9499\,f\,|T|$, and $T$ otherwise.
--
--   **Statement.** The output $S=\mathcal A(I,f)$ is a nonempty list of distinct facilities of $I$, and
--
--   $$\mathrm{cost}(S)\ \le\ 1.9499\,\big(\mathrm{OPT}_f-f\,|S|\big).$$
--
--   **Role.** Together with the polynomial running time of $\mathcal A$, this is Theorem 1.4: the main theorem on facility location is witnessed by $\mathcal A$. It combines the bound for the trivial solution in the degenerate cases with the bound for the greedy run in the others.
--
--   **Formalization Note** The algorithm works in exact rational arithmetic on the encoded instance. Division by zero is $0$ in Lean, so the greedy run is defined also when $t=0$ ($f=0$, or no positive client–facility distance); these cases are covered by the trivial solution. $|S|$ is the length of the output list.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Theorem 1.4 (Theorem 4.3 in full). Lean source: `BCFGJPSSV26.FL.alg_spec`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/FL/Main.lean#L37-L65

module

public import Definitions.Def_BCFGJPSSV26_FL_Run
public import Definitions.Def_BCFGJPSSV26_FL_PolyTime
public import Definitions.Def_BCFGJPSSV26_FL_Main

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.FL

open Encoding

variable {I : Instance}

open Greedy in

theorem alg_spec (hI : I.Valid) (hn : 0 < I.n) {f : ℚ} (hf : 0 ≤ f) :
    I.IsCenterList (alg (toRaw I) f) ∧
      I.cost (I.centers (alg (toRaw I) f)) ≤
        1.9499 * (I.optFL (f : ℝ) - (f : ℝ) * (alg (toRaw I) f).length) := by sorry

end BCFGJPSSV26.FL
end
