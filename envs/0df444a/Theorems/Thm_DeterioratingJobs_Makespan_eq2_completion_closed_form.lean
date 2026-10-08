-- Prove2me | Theorems.Thm_DeterioratingJobs_Makespan_eq2_completion_closed_form
-- name    : DeterioratingJobs.Makespan.eq2_completion_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:08:06.77979+00:00
-- url     : https://prove2.me/theorems/752c4d15-cfde-4d53-b498-aba0e468afc2
-- title:
--   Eq. (2) — $S_j=\sum_{i\le j} X_i\prod_{r=i+1}^{j}(1+\alpha_r)$ along any schedule
-- statement:
--   In the linear deterioration model (initial requirements $X_i$, growth rates $\alpha_i$, completion times $S_k(\pi)$ defined by $S_0(\pi)=0$ and $S_k(\pi)=S_{k-1}(\pi)+X_{\pi(k)}+\alpha_{\pi(k)}S_{k-1}(\pi)$), for every schedule $\pi$, every $j\in\{0,1,\dots,N\}$ and every outcome $\omega$,
--
--   $$
--   S_j(\pi) = \sum_{i=1}^{j} X_{\pi(i)} \prod_{r=i+1}^{j} \bigl(1+\alpha_{\pi(r)}\bigr),
--   $$
--
--   where an empty product is $1$ (and the empty sum, at $j=0$, is $0$).
--
--   The paper writes this for the policy $\pi_0=(1,2,\dots,N)$ "for notational convenience"; for a general $\pi$ it is the same formula with job indices relabelled along $\pi$. It exhibits the makespan $S_N$ as the sum of the delays that each initial requirement causes to all later jobs.
--
--   **Formalization Note** Positions are 0-based in Lean: the sum is over positions `i` with `i < j` and the product over positions `r` with `i < r < j`. The identity holds pointwise in $\omega$ and for every real $\alpha$; no sign or measurability condition is needed.
-- source:
--   Browne, Yechiali, Scheduling Deteriorating Jobs on a Single Processor, Oper. Res. 38 (1990), p. 496, Section 1, Eq. (2)

import Mathlib
import Definitions.Def_DeterioratingJobs_Makespan_Model

namespace DeterioratingJobs.Makespan

/-- Eq. (2) (Browne–Yechiali 1990, p. 496), along an arbitrary schedule `π`: for every `k ≤ N`,
`S_k(π) = ∑_{i < k} X_{π(i)} ∏_{i < r < k} (1 + α_{π(r)})` (positions 0-based; empty product `= 1`). -/
theorem eq2_completion_closed_form {Ω : Type*} {N : ℕ} (X : Fin N → Ω → ℝ) (α : Fin N → ℝ)
    (π : Equiv.Perm (Fin N)) (k : ℕ) (hk : k ≤ N) (ω : Ω) :
    completionTime X α π k ω =
      ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k),
        X (π i) ω * ∏ r ∈ Finset.univ.filter (fun r : Fin N => i < r ∧ r.val < k),
          (1 + α (π r)) := by sorry

end DeterioratingJobs.Makespan
