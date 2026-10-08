-- Prove2me | Theorems.Thm_FlowJobHardness_FlowShopGap_theorem_1_1
-- name    : FlowJobHardness.FlowShopGap.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:34:09.077793+00:00
-- url     : https://prove2.me/theorems/9955d81a-2787-46dc-a23d-fb2e3e434ea2
-- title:
--   Theorem 1.1 (explicit form) — every schedule of $F(r,d)$ has makespan at least $\min(r,d/4)\cdot\mathrm{lb}$, with $\mathrm{lb}=r^{2d}$
-- statement:
--   Let $r\ge8$ and $d$ be natural numbers and let $F(r,d)$ be the flow shop instance of Section 2.2.1. Then
--
--   1. every job of $F(r,d)$ has length $r^{2d}$ and every machine has load $r^{2d}$, so that $\mathrm{lb}=\max(C,D)=r^{2d}$;
--   2. every feasible schedule $s$ of $F(r,d)$ has makespan
--   $$C_{\max}(s)\ \ge\ r^{2d}\cdot\min\Bigl(r,\ \frac d4\Bigr)=\mathrm{lb}\cdot\min\Bigl(r,\ \frac d4\Bigr).$$
--
--   The paper states Theorem 1.1 as "there exist flow shop instances with optimal makespan $\Omega(\mathrm{lb}\cdot\log\mathrm{lb}/\log\log\mathrm{lb})$". Its proof (§2.2.2) establishes the explicit bound above for every feasible schedule, and then takes $r=d$: then $\mathrm{lb}=d^{2d}$ and $d=\Theta(\log\mathrm{lb}/\log\log\mathrm{lb})$. The explicit bound is what is formalized; the asymptotic corollary is not.
--
--   The result answers negatively the question of Feige and Scheideler whether flow shops always admit schedules of length $O(\mathrm{lb})$: the trivial lower bound can be off by an unbounded factor.
--
--   **Formalization Note** The model is the published job shop model `JobShopLTAS.Core.Instance`; a feasible schedule has nonnegative start times, chain precedence within each job, and pairwise non-overlapping operations on each machine (so a zero-length operation cannot sit strictly inside another operation on its machine). The makespan is the largest completion time of an operation. The threshold $r\ge8$ makes explicit the paper's "sufficiently large $r$". For $d=0$ the instance is empty and the bound reads $0\le0$.
-- source:
--   Mastrolilli, Svensson, Hardness of Approximating Flow and Job Shop Scheduling Problems, J. ACM 58(5) (2011), Article 20, p. 20:4, Theorem 1.1; explicit form from §2.2.2, pp. 20:10-20:11

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobHardness_FlowShopGap_Construction

open JobShopLTAS.Core

namespace FlowJobHardness.FlowShopGap

/-- Theorem 1.1 (p. 20:4), in the explicit form its proof (§2.2.2) gives: for every `r ≥ 8`
and every `d`, in the flow shop instance `F(r, d)` every job has length `r^{2d}` and every
machine has load `r^{2d}` (so `lb = r^{2d}`), and every feasible schedule has makespan at
least `min(r, d/4) · r^{2d}`. -/
theorem theorem_1_1 (r d : ℕ) (hr : 8 ≤ r) :
    (∀ q : Fin (size r d), (inst r d).jobLength q = (r : ℝ) ^ (2 * d)) ∧
      (∀ t : Fin (size r d), (inst r d).load t = (r : ℝ) ^ (2 * d)) ∧
      ∀ s : (inst r d).Op → ℝ, (inst r d).IsFeasibleSchedule Finset.univ s →
        (r : ℝ) ^ (2 * d) * min (r : ℝ) ((d : ℝ) / 4) ≤ (inst r d).makespan Finset.univ s := by sorry

end FlowJobHardness.FlowShopGap
