-- Prove2me | Theorems.Thm_AssortOpt_HMF_theorem_2
-- name    : AssortOpt.HMF.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:28.504247+00:00
-- url     : https://prove2.me/theorems/ceb7dbb3-ad86-4acd-9b4e-8ec52b8c7cc3
-- title:
--   Theorem 2, p. 18 — under history-monotone futures, some assortment attains the maximum revenue over all IC mechanisms (OPT^S = OPT^x)
-- statement:
--   Let $\mathcal L, p$ be a list distribution over items $N = \{1, \dots, n\}$ with **history-monotone futures**: for all realizable prefixes $\rho, \rho'$ with the same endpoint and $\rho_{\mathrm{pre}} \not\subseteq \rho'_{\mathrm{pre}}$ as sets, the future from $\rho$ dominates the future from $\rho'$. Then for any prices $r_1, \dots, r_n \ge 0$, assortments are optimal within the larger class of IC mechanisms: there is an assortment $S \subseteq N$ such that
--   $$\mathsf{REV}[S] = \max\{\mathsf{REV}[x] : x \text{ satisfies (3)–(5)}\} = \mathsf{OPT}^x,$$
--   so $\mathsf{OPT}^S = \mathsf{OPT}^x$.
--
--   This is the paper's main result. No lottery or other incentive-compatible selling mechanism can earn more than the best assortment under any choice model with history-monotone futures, which include Markov Chain choice models (and hence MNL), Elimination by Aspects, and MNL mixed with singleton lists. For general list distributions the conclusion fails (Example 1, p. 2).
--
--   **Formalization Note** The conclusion is `IsGreatest`: $\mathsf{REV}[S]$ is the revenue of some IC mechanism and no IC mechanism earns more. The condition is on the distribution only and precedes the prices.
--
--   Differences from the source:
--   - encoding: items $\{1,\dots,n\}$, lists, support $\mathcal L$ with weights $p$ → `Fin n` (0-based), `ListDist` (finite support of `Nodup` lists, $p > 0$ on $\mathcal L$, $\sum p = 1$); reason: same instances.
--   - reading: "assortments are optimal within the larger class of IC mechanisms" → some $S$ has $\mathsf{REV}[S]$ equal to the greatest value of $\mathsf{REV}[x]$ over IC $x$; reason: p. 10 states the question as $\mathsf{OPT}^S = \mathsf{OPT}^x$; the LP optimum is attained (compact feasible set).
-- source:
--   Ma, When is Assortment Optimization Optimal?, arXiv:2105.10433v5, p. 18, Theorem 2

import Mathlib
import Definitions.Def_AssortOpt_HMF_Setting

namespace AssortOpt.HMF

theorem theorem_2 {n : ℕ} (D : ListDist n) (hD : HasHistoryMonotoneFutures D)
    (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j) :
    ∃ S : Finset (Fin n), IsGreatest (revMech D r '' {x | IsIC D x}) (revAssort D r S) := by sorry

end AssortOpt.HMF
