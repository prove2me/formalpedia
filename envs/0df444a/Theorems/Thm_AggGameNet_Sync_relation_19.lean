-- Prove2me | Theorems.Thm_AggGameNet_Sync_relation_19
-- name    : AggGameNet.Sync.relation_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:36:40.025601+00:00
-- url     : https://prove2.me/theorems/1be94da8-0983-4ccc-9b91-c5ebd88500e9
-- title:
--   Relation (19), p. 14 — one-step squared-distance estimate
-- statement:
--   Let the strategy sets $K_i$ be nonempty, compact and convex with $F_i$ continuous on $K_i\times\bar K$ (Assumption 1), let $x^*$ solve $\operatorname{VI}(K,\phi)$, and let $(x^k,v^k)$ follow the synchronous projection and estimate recursions with nonnegative stepsizes and column-stochastic weights. Suppose $\|F_i(x_i^k,N\hat v_i^k)\|\le C$, $\|F_i(\xi,u)\|\le F_{\max}$ for $\xi\in K_i,u\in\bar K$, $\|\xi\|\le M$ for $\xi\in K_i$, and the aggregate Lipschitz constants are $\bar L_i$. Then for every $k$,
--
--   $$\sum_i\|x_i^{k+1}-x_i^*\|^2\le\sum_i\|x_i^k-x_i^*\|^2+N(2C^2+2F_{\max}^2)\alpha_k^2+4\alpha_kMN\sum_i\bar L_i\|\hat v_i^k-y^k\|-2\alpha_k\sum_i(\phi_i(x^k)-\phi_i(x^*))^\top(x_i^k-x_i^*).$$
--
--   This is the paper's descent estimate, with $\tilde C=2C^2+2F_{\max}^2$.
--
--   **Formalization Note** Assumption 3 applies to all aggregate arguments because $N\hat v_i^k$ need not lie in $\bar K$. Any uniform upper bound $F_{\max}$ is permitted; the paper uses its least value, the maximum over the compact feasible sets.
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, relation (19), proof of Proposition 2, pp. 13–14

import Mathlib
import Definitions.Def_AggGameNet_Sync_Setting

namespace AggGameNet.Sync

/-- Relation (19), proof of Proposition 2, p. 14. -/
theorem relation_19 {N n : ℕ} (hN : 0 < N)
    (K : Fin N → Set (E n)) (F : Fin N → E n → E n → E n)
    (h1 : Assumption1 K F)
    (Lbar : Fin N → ℝ) (h3 : Assumption3 K F Lbar)
    (W : ℕ → Matrix (Fin N) (Fin N) ℝ) (α : ℕ → ℝ)
    (x v : ℕ → Fin N → E n) (hrun : IsSyncRun K F W α x v)
    (hcol : ∀ k i, ∑ j, W k j i = 1)
    (hα : ∀ k, 0 ≤ α k)
    (xs : Fin N → E n) (hxs : IsVISol K F xs)
    (C Fmax M : ℝ)
    (hC : ∀ i k, ‖F i (x k i) ((N : ℝ) • vhat W v k i)‖ ≤ C)
    (hF : ∀ i, ∀ xi ∈ K i, ∀ u ∈ Kbar K, ‖F i xi u‖ ≤ Fmax)
    (hM : ∀ i, ∀ a ∈ K i, ‖a‖ ≤ M) :
    ∀ k,
      (∑ i, ‖x (k + 1) i - xs i‖ ^ 2) ≤
        (∑ i, ‖x k i - xs i‖ ^ 2) +
        (N : ℝ) * (2 * C ^ 2 + 2 * Fmax ^ 2) * α k ^ 2 +
        4 * α k * M * (N : ℝ) *
          (∑ i, Lbar i * ‖vhat W v k i - yavg v k‖) -
        2 * α k *
          (∑ i, inner ℝ (phi F (x k) i - phi F xs i) (x k i - xs i)) := by sorry

end AggGameNet.Sync
