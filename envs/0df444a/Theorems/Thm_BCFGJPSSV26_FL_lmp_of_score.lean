-- Prove2me | Theorems.Thm_BCFGJPSSV26_FL_lmp_of_score
-- name    : BCFGJPSSV26.FL.lmp_of_score
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:39:53.01904+00:00
-- url     : https://prove2.me/theorems/224549df-be18-4bee-b666-01a0b928c68c
-- title:
--   The LMP guarantee as a bound on the objective $\mathrm{cost}(S)+1.9499\,f\,|S|$
-- statement:
--   This lemma rewrites the LMP guarantee of Theorem 1.4 of Part I (arXiv:2610.18144) as a bound on a single objective: $\mathrm{cost}(S)+\lambda f|S|\le\lambda\,\mathrm{OPT}_f$ gives $\mathrm{cost}(S)\le\lambda\,(\mathrm{OPT}_f-f|S|)$, for $\lambda=1.9499$.
--
--   **Setting.** Let $I$ be an instance with $n$ clients, $m$ facilities and rational distances. For a nonempty set $S$ of facilities, $\mathrm{cost}(S)=\sum_j\min_{i\in S}d(j,i)$ over the clients $j$, and for an opening cost $f$,
--
--   $$\mathrm{OPT}_f=\inf_{S'\ne\emptyset}\big(\mathrm{cost}(S')+f\,|S'|\big).$$
--
--   **Statement.** Let $S$ be a nonempty list of distinct facilities of $I$ and let $f$ be a rational number. If
--
--   $$\mathrm{cost}(S)+1.9499\,f\,|S|\ \le\ 1.9499\,\mathrm{OPT}_f ,$$
--
--   then
--
--   $$\mathrm{cost}(S)\ \le\ 1.9499\,\big(\mathrm{OPT}_f-f\,|S|\big).$$
--
--   **Role.** The facility-location algorithm chooses, among the greedy run and the trivial solution, the candidate with the smaller objective $\mathrm{cost}(S)+1.9499\,f\,|S|$. The proof of Theorem 1.4 bounds this objective for one of the two candidates, hence for the output, and this lemma turns that bound into the guarantee of the theorem.
--
--   **Formalization Note** In the hypothesis the left side is the rational number that the algorithm computes from the encoded instance; for a nonempty list of facilities it equals $\mathrm{cost}(S)+1.9499\,f\,|S|$, with $|S|$ the length of the list. Neither validity of the instance nor $f\ge0$ is assumed.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172). Lean source: `BCFGJPSSV26.FL.lmp_of_score`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/FL/Select.lean#L101-L107

module

public import Definitions.Def_BCFGJPSSV26_FL_Algorithm
public import Definitions.Def_BCFGJPSSV26_FL_Select

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.FL

open Finset Greedy

variable {I : Instance}

theorem lmp_of_score {S : List ℕ} (hS : I.IsCenterList S) {f : ℚ}
    (h : (score (toRaw I) f S : ℝ) ≤ (lmpC : ℝ) * I.optFL f) :
    I.cost (I.centers S) ≤ 1.9499 * (I.optFL (f : ℝ) - (f : ℝ) * S.length) := by sorry

end BCFGJPSSV26.FL
end
