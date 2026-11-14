-- Prove2me | Theorems.Thm_BCFGJPSSV26_FL_score_trivialSol_le
-- name    : BCFGJPSSV26.FL.score_trivialSol_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:39:18.378222+00:00
-- url     : https://prove2.me/theorems/00e6821f-cdcf-4b61-899a-26cdfbdeec68
-- title:
--   The trivial solution meets the LMP bound when it is no larger than an optimal set, or $f=0$
-- statement:
--   This lemma covers the degenerate cases of Theorem 1.4 of Part I (arXiv:2610.18144): the trivial solution satisfies the bound on the objective $\mathrm{cost}(S)+\lambda f|S|$, $\lambda=1.9499$, whenever it has at most as many facilities as an optimal set, or the opening cost is $0$.
--
--   **Setting.** Let $I$ be a valid instance: $n$ clients, $m\ge1$ facilities and rational distances forming a pseudometric on the $n+m$ points. For a nonempty set $S$ of facilities, $\mathrm{cost}(S)=\sum_j\min_{i\in S}d(j,i)$ over the clients $j$, and for an opening cost $f$,
--
--   $$\mathrm{OPT}_f=\min_{S'\ne\emptyset}\big(\mathrm{cost}(S')+f\,|S'|\big).$$
--
--   The *trivial solution* $T$ is the list, without repetitions, of the nearest facility of every client (the facility of least index among the nearest ones).
--
--   **Statement.** Assume $n\ge1$, let $f\ge0$ be rational, and let $O$ be a nonempty set of facilities that is optimal, that is, $\mathrm{OPT}_f=\mathrm{cost}(O)+f\,|O|$. If $|T|\le|O|$ or $f=0$, then
--
--   $$\mathrm{cost}(T)+1.9499\,f\,|T|\ \le\ 1.9499\,\mathrm{OPT}_f .$$
--
--   **Role.** In the proof of Theorem 1.4 this handles the cases where the greedy run is not used: $n=1$, $m=1$, an optimal set of cost $0$ (then $|T|\le|O|$), and $f=0$. In all other cases $n,m\ge2$, $f>0$ and $\mathrm{cost}(O)>0$, and the greedy run meets the same bound. The algorithm outputs the candidate with the smaller objective, and the bound on the objective is equivalent to the LMP guarantee $\mathrm{cost}(S)\le1.9499\,(\mathrm{OPT}_f-f|S|)$.
--
--   **Formalization Note** The left side is the rational number that the algorithm computes from the encoded instance, which equals $\mathrm{cost}(T)+1.9499\,f\,|T|$; $|T|$ is the length of the list.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172). Lean source: `BCFGJPSSV26.FL.score_trivialSol_le`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/FL/Select.lean#L109-L127

module

public import Definitions.Def_BCFGJPSSV26_FL_Algorithm
public import Definitions.Def_BCFGJPSSV26_FL_Select

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.FL

open Finset Greedy

variable {I : Instance}

theorem score_trivialSol_le (hI : I.Valid) (hn : 1 ≤ I.n) {f : ℚ} (hf : 0 ≤ f)
    {O : Finset (Fin I.m)} (hO : O.Nonempty) (hopt : I.optFL f = I.cost O + f * O.card)
    (h : (trivialSol (toRaw I)).length ≤ O.card ∨ f = 0) :
    (score (toRaw I) f (trivialSol (toRaw I)) : ℝ) ≤ (lmpC : ℝ) * I.optFL f := by sorry

end BCFGJPSSV26.FL
end
