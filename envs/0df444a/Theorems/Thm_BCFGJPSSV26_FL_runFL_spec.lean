-- Prove2me | Theorems.Thm_BCFGJPSSV26_FL_runFL_spec
-- name    : BCFGJPSSV26.FL.runFL_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:39:02.19881+00:00
-- url     : https://prove2.me/theorems/d33dfa2d-f02e-43e7-a030-f98b1adcde53
-- title:
--   LMP bound for the greedy run of the facility-location algorithm
-- statement:
--   This is the guarantee of the greedy run in the proof of Theorem 1.4 of Part I (arXiv:2610.18144): one run of the log-adaptive greedy algorithm on a rescaled instance satisfies the LMP bound with factor $\lambda=1.9499$ against every set of positive cost.
--
--   **Setting.** Let $I$ be a valid instance: $n$ clients, $m$ facilities and rational distances forming a pseudometric on the $n+m$ points. For a nonempty set $S$ of facilities, $\mathrm{cost}(S)=\sum_j\min_{i\in S}d(j,i)$ over the clients $j$. Let $f$ be a rational opening cost.
--
--   The *greedy run* $G=G(I,f)$ is defined as follows. Let $d_{\min}$ be the least positive client–facility distance and $t=\min\big(d_{\min}/(10^5n),\,f\big)$. The client–facility distances are replaced by $d(j,i)/t+1$, and CompleteSolution of the greedy algorithm of Part I, Section 5 (exact openability tests, bid $[\alpha-1.224\,d]^+$, $\delta=10^{-6}$, the paper's $\varepsilon=\delta/10$) is run from the empty solution at the scaled opening cost $\hat f=\lambda\,(1-\delta)\,f/t$. $G$ is the list of the facilities it opens, without repetitions.
--
--   **Statement.** Assume $n\ge2$, $m\ge2$ and $f>0$, and let $O$ be a nonempty set of facilities with $\mathrm{cost}(O)>0$. Then $G$ is a nonempty list of distinct facilities of $I$, and
--
--   $$\mathrm{cost}(G)+\lambda\,f\,|G|\ \le\ \lambda\,\big(\mathrm{cost}(O)+f\,|O|\big),\qquad\lambda=1.9499 .$$
--
--   **Role.** Applied to an optimal set $O$ for $\mathrm{OPT}_f$, this is the case of Theorem 1.4 in which the trivial solution (the nearest facility of every client) does not suffice; in the remaining cases ($n=1$, $m=1$, $f=0$ or $\mathrm{cost}(O)=0$) the trivial solution meets the bound. The inequality comes from the robust LMP guarantee (Part I, Theorem D.7) of the analysis of Theorem 1.2, applied in the rescaled instance with slack $0$.
--
--   **Formalization Note** The left side is the objective that the algorithm computes exactly in rational arithmetic; for a list of distinct facilities it equals $\mathrm{cost}(G)+\lambda f|G|$, with $|G|$ the length of the list.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172). Lean source: `BCFGJPSSV26.FL.runFL_spec`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/FL/Run.lean#L338-L438

module

public import Definitions.Def_BCFGJPSSV26_FL_Select
public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Core
public import Definitions.Def_BCFGJPSSV26_FL_Run

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.FL

open Finset Greedy

variable {I : Instance}

theorem runFL_spec (hI : I.Valid) (hn : 2 ≤ I.n) (hm : 2 ≤ I.m) {f : ℚ} (hf : 0 < f)
    {O : Finset (Fin I.m)} (hO : O.Nonempty) (hc : 0 < I.cost O) :
    I.IsCenterList (runFL (toRaw I) f) ∧
      (score (toRaw I) f (runFL (toRaw I) f) : ℝ) ≤ (lmpC : ℝ) * (I.cost O + f * O.card) := by sorry

end BCFGJPSSV26.FL
end
