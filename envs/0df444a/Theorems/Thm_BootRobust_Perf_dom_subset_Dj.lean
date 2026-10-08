-- Prove2me | Theorems.Thm_BootRobust_Perf_dom_subset_Dj
-- name    : BootRobust.Perf.dom_subset_Dj
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:06.288983+00:00
-- url     : https://prove2.me/theorems/d5cd83a0-4d18-40c5-b4d8-b117715c2762
-- title:
--   (23), p. 11 — the domain of the partial estimator (22) lies in D^j_n, and off D^j_n the partial estimator is −∞
-- statement:
--   Fix $n,k\in\mathbb N$, a chain of neighbourhoods $N^0,N^1,\dots\subseteq\Omega_n$, weights $w$, losses $\ell$ and an index $j$. Let $D\in\mathbb R^{\Omega_n}$.
--
--   1. If the constraints of the linear program (22) defining the partial estimator $E^{n,j}_D$ are feasible for some $(s,P)$, then $D\in\mathcal D^j_n$.
--   2. Consequently, if $D\notin\mathcal D^j_n$, then
--   $$E^{n,j}_D=-\infty .$$
--
--   This is the inclusion $\operatorname{dom}E^{n,j}_D\subseteq\mathcal D^j_n$ of (23), with the convention that the supremum over an empty set is $-\infty$. It is used to restrict the event of Theorem 6 to the sets $\mathcal D^j_n$.
--
--   **Formalization Note** No hypothesis on $n,k,N,w$ is needed; the statement holds for every real vector $D$ (feasibility forces $D\in\mathcal D_n$).
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, arXiv:1711.09974v2, (22) and (23), p. 11

import Mathlib
import Definitions.Def_BootRobust_Perf_Setting

namespace BootRobust.Perf

/-- (23), p. 11: every distribution `D` at which the linear program (22) is feasible lies in
`D^j_n`; hence off `D^j_n` the partial estimator is the supremum over the empty set, `⊥`. -/
theorem dom_subset_Dj {ι : Type*} [Fintype ι] [DecidableEq ι] (n k : ℕ) (N : ℕ → Finset ι)
    (w ℓ : ι → ℝ) (j : ℕ) (D : ι → ℝ) :
    (∀ (s : ℝ) (P : ι → ℝ), lpFeasible n k N w j D s P → D ∈ Dj n k N j) ∧
      (D ∉ Dj n k N j → partialEst n k N w ℓ j D = ⊥) := by sorry

end BootRobust.Perf
