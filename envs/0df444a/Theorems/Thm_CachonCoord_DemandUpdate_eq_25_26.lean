-- Prove2me | Theorems.Thm_CachonCoord_DemandUpdate_eq_25_26
-- name    : CachonCoord.DemandUpdate.eq_25_26
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:45:42.040772+00:00
-- url     : https://prove2.me/theorems/36b0a181-f98b-4ce7-8596-41b37aaa0428
-- title:
--   Eqs. (25)–(26), p. 64 — F(q₂(ξ)|ξ) = (p − c₂)/p, q₂(ξ) increasing, and ξ(q₁) partitions the signals
-- statement:
--   In the newsvendor with demand updating, let $q_2(\xi) \ge 0$ solve
--   $$F(q_2(\xi)\,|\,\xi) = \frac{p-c_2}{p} \qquad (25)$$
--   for every signal $\xi \ge 0$. Then:
--
--   1. with no inventory at the start of period 2, $q \ge 0$ maximizes $\Omega_2(\cdot\,|\,0,\xi)$ over $q \ge 0$ if and only if $F(q\,|\,\xi) = (p-c_2)/p$;
--   2. $q_2(\xi)$ is strictly increasing in $\xi$;
--   3. if $\xi(q_1) \ge 0$ solves $F(q_1\,|\,\xi(q_1)) = (p-c_2)/p$ (Eq. (26)), then for every $\xi \ge 0$, $q_2(\xi) > q_1$ if and only if $\xi > \xi(q_1)$;
--   4. for $q_1, \xi \ge 0$ the supply chain's period-2 problem $\max_{q_2 \ge q_1} \Omega_2(q_2\,|\,q_1,\xi)$ has the unique solution $q_2(q_1,\xi) = \max(q_1, q_2(\xi))$;
--   5. the partition: if $\xi > \xi(q_1)$, every optimal $q_2$ exceeds $q_1$, so the optimal period-2 order is positive; if $\xi \le \xi(q_1)$, ordering nothing ($q_2 = q_1$) is optimal.
--
--   This is the structure of the supply chain's period-2 decision, on which the derivative (27) of $\Omega_1$ rests.
--
--   **Formalization Note** The page assumes strict concavity of $\Omega_2$ in $q_2$; here it follows from the model's strictly increasing $F(\cdot\,|\,\xi)$. Existence of $q_2(\xi)$ and of $\xi(q_1)$ are hypotheses, as the page assumes them; (26) need not have a solution for every $q_1$.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.6.1, Eqs. (25)–(26), p. 64

import Mathlib
import Definitions.Def_CachonCoord_DemandUpdate_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.DemandUpdate

open Model

/-- Cachon (2003), 3rd draft, §6.6.1, Eqs. (25)–(26), p. 64. Let `q2bar ξ = q_2(ξ)` solve (25),
`F(q_2(ξ)|ξ) = (p − c_2)/p`, for every signal `ξ ≥ 0`. Then
1. (25): with no inventory (`q_1 = 0`), `q ≥ 0` maximizes `Ω_2(·|0, ξ)` over `q ≥ 0` iff
   `F(q|ξ) = (p − c_2)/p`;
2. `q_2(ξ)` is (strictly) increasing in `ξ`;
3. if `ξ(q_1) = xi1` solves (26), `F(q_1|ξ(q_1)) = (p − c_2)/p`, then `q_2(ξ) > q_1` iff `ξ > ξ(q_1)`;
4. the constrained period-2 optimum over `q_2 ≥ q_1` is unique and equals `max(q_1, q_2(ξ))`;
5. the partition: if `ξ > ξ(q_1)` every optimal period-2 order is positive (`q_2 > q_1`);
   otherwise ordering nothing (`q_2 = q_1`) is optimal. -/
theorem eq_25_26 (M : Model) (q2bar : ℝ → ℝ)
    (hq2bar : ∀ ξ, 0 ≤ ξ → 0 ≤ q2bar ξ ∧ M.F ξ (q2bar ξ) = M.ratio) :
    (∀ ξ q, 0 ≤ ξ →
      ((0 ≤ q ∧ IsMaxOn (M.Omega2 0 ξ) (Set.Ici 0) q) ↔ (0 ≤ q ∧ M.F ξ q = M.ratio))) ∧
    StrictMonoOn q2bar (Set.Ici 0) ∧
    (∀ q1 xi1 ξ, 0 ≤ q1 → 0 ≤ xi1 → M.F xi1 q1 = M.ratio → 0 ≤ ξ →
      (q1 < q2bar ξ ↔ xi1 < ξ)) ∧
    (∀ q1 ξ, 0 ≤ q1 → 0 ≤ ξ →
      IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) (max q1 (q2bar ξ)) ∧
      ∀ q, q1 ≤ q → IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) q → q = max q1 (q2bar ξ)) ∧
    (∀ q1 xi1 ξ, 0 ≤ q1 → 0 ≤ xi1 → M.F xi1 q1 = M.ratio → 0 ≤ ξ →
      (xi1 < ξ → ∀ q, q1 ≤ q → IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) q → q1 < q) ∧
      (ξ ≤ xi1 → IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) q1)) := by sorry

end CachonCoord.DemandUpdate
