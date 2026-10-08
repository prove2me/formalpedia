-- Prove2me | Theorems.Thm_DelayedSWPT_Extended_doubled_opt_eq_two_mul
-- name    : DelayedSWPT.Extended.doubled_opt_eq_two_mul
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:08:58.732813+00:00
-- url     : https://prove2.me/theorems/6adb0f3f-d9e7-4131-8d0d-de254aeb409c
-- title:
--   Lemma 1 — the doubled problem (2P) has exactly twice the optimal value of (P)
-- statement:
--   Let (P) be an instance with integer release dates $r_j$, processing times $p_j \ge 1$ and weights $w_j > 0$, and let (2P) be the doubled instance with data $(2r_j, 2p_j, w_j)$. If $\pi^*$ is an optimal schedule for (P) and $\mu^*$ is an optimal schedule for (2P), then
--
--   $$\sum_{j\in J} w_j C_j(\mu^*) = 2 \sum_{j\in J} w_j C_j(\pi^*).$$
--
--   Combined with the optimality of $\pi_E$ for the extended problem, this turns a comparison with an optimal schedule of (2P) into the factor 2 against the optimum of (P).
--
--   **Formalization Note** Optimality is among all feasible schedules with integer start times, for both problems; completion times in (2P) are $\mu^*_j + 2p_j$.
-- source:
--   Anderson and Potts, Online Scheduling of a Single Machine to Minimize Total Weighted Completion Time, Math. Oper. Res. 29(3) (2004), p. 689, Lemma 1

import Mathlib
import Definitions.Def_DelayedSWPT_Extended_Problem

namespace DelayedSWPT.Extended

open DelayedSWPT.Model

/-- Lemma 1 of Anderson and Potts (2004), p. 689: if `π*` and `μ*` are optimal schedules for
(P) and (2P), then `∑ⱼ wⱼ Cⱼ(μ*) = 2 ∑ⱼ wⱼ Cⱼ(π*)`. -/
theorem doubled_opt_eq_two_mul {n : ℕ} (I : Instance n) (πstar μstar : Fin n → ℕ)
    (hπ : IsOptimal I.r I.p I.w πstar)
    (hμ : IsOptimal (double I).r (double I).p (double I).w μstar) :
    cost (double I).w (double I).p μstar = 2 * cost I.w I.p πstar := by sorry

end DelayedSWPT.Extended
