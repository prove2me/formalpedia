-- Prove2me | Theorems.Thm_BondVoting_Sybil_sybil_step
-- name    : BondVoting.Sybil.sybil_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:48.189908+00:00
-- url     : https://prove2.me/theorems/fbcc7c5e-4668-4385-97f1-2e145886947b
-- title:
--   Proof of Proposition 2, p. 25 — a Sybil attack does no better than one entity at t*_i
-- statement:
--   Let $r > 0$, $T > 0$, and let an agent of type $(\theta, u, r_i)$ with $|u|\theta > 1$, $r < r_i < \theta|u| r$ and budget $q > 0$ have optimal bond length $t^*_i$ from equation (6). Take any feasible Sybil attack: stakes $q_1, \dots, q_M \ge 0$ with $\sum_m q_m \le q$ and commitments $t_1, \dots, t_M \in (0, T]$. Then
--   $$\sum_{m=1}^{M} \pi_i(q_m, t^*_i) = \pi_i\Bigl(\sum_{m=1}^{M} q_m,\ t^*_i\Bigr) \qquad\text{and}\qquad \sum_{m=1}^{M} \pi_i(q_m, t_m) \le \pi_i(q, t^*_i).$$
--
--   So splitting the budget over identities, whatever their commitments, earns at most what the agent earns as a single entity at her optimal bond length: this is the Sybil-resistance step of the proof of Proposition 2.
--
--   **Formalization Note.** The page writes "$= \pi_i(q_i, t^*_i)$", which presumes $\sum_m q_{im} = q_i$; under Definition 5(a)'s $\sum_m q_{im} \le q_i$ the second conclusion is an inequality. The hypothesis $r_i < \theta|u| r$ restricts to the cases of Proposition 1 that have a maximizer.
-- source:
--   Mohan, Khezr & Berg, Voting with time commitment for decentralized governance: Bond voting as a Sybil-resistant mechanism, SSRN 4259599 (PDF of 2024-02-20), p. 25, proof of Proposition 2

import Mathlib
import Definitions.Def_BondVoting_Sybil_Model

namespace BondVoting.Sybil
theorem sybil_step (r θ u ri T q : ℝ) (hr : 0 < r) (hT : 0 < T)
    (hadm : Admissible r θ u ri) (hq : 0 < q) (hint : ri < θ * |u| * r)
    (M : ℕ) (qs τ : Fin M → ℝ) (hfeas : FeasibleAttack q T M qs τ) :
    ∑ m, bondPayoff r θ u ri (qs m) (tStar r θ u ri T) =
        bondPayoff r θ u ri (∑ m, qs m) (tStar r θ u ri T) ∧
      attackPayoff (bondPayoff r θ u ri) qs τ ≤ bondPayoff r θ u ri q (tStar r θ u ri T) := by sorry
end BondVoting.Sybil
