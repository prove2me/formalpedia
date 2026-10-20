-- Prove2me | Theorems.Thm_AdBlocking_Surplus_thresholds
-- name    : AdBlocking.Surplus.thresholds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:56.975973+00:00
-- url     : https://prove2.me/theorems/604e78ec-ee3a-4333-b15d-a4ee9afe5b39
-- title:
--   §3.2, p. 20 (PDF 21) — thresholds: at r = 1 surplus rises iff t > 4/5; at t = 1 iff r > (√141 − 1)/14
-- statement:
--   Compare total consumer surplus at the equilibrium with the adblocker, $CS_{AB}$, and at the benchmark equilibrium without it, $CS_{NA}$, for a sufficiently large download-cost support $\bar\kappa$.
--
--   1. When quality sensitivity is homogeneous ($t=1$) and $0<r\le1$: if $r>(\sqrt{141}-1)/14$ then $CS_{AB}>CS_{NA}$, and if $r\le(\sqrt{141}-1)/14$ then $CS_{AB}<CS_{NA}$.
--   2. When ad sensitivity is homogeneous ($r=1$) and $0\le t\le1$: if $t>4/5$ then $CS_{AB}>CS_{NA}$, and if $t\le 4/5$ then $CS_{AB}<CS_{NA}$.
--
--   $$CS_{AB}>CS_{NA}\iff\begin{cases} r>\tfrac{\sqrt{141}-1}{14} & (t=1),\\ t>\tfrac45 & (r=1),\end{cases}\qquad\text{for all large }\bar\kappa.$$
--
--   Each comparison holds for every $\bar\kappa$ beyond a threshold depending on $(p_a,c,r,t)$, at every equilibrium: every benchmark-optimal ad rule, every optimal adblocker limit rule, and every optimal quality in each regime. These two boundary lines make the "sufficiently high" of Proposition 3 explicit.
--
--   **Formalization Note** At $t=1$ (resp. $r=1$) the corresponding sensitivity is a point mass at $1$. The page says "increases if and only if"; at the threshold itself the surplus with the adblocker is strictly lower, so the "only if" side is stated as a strict decrease. The page writes "$\kappa$ high enough"; this means the support bound $\bar\kappa$.
-- source:
--   Gritckevich, Katona & Sarvary, Ad Blocking, SSRN 3100524 (version of March 7, 2021), p. 20 (PDF 21), §3.2, paragraph after Proposition 3

import Mathlib
import Definitions.Def_AdBlocking_Surplus_Model

namespace AdBlocking.Surplus

theorem thresholds :
    (∀ pa c r : ℝ, Standing pa c r 1 →
      ((Real.sqrt 141 - 1) / 14 < r →
        ∃ K : ℝ, 0 < K ∧ ∀ κbar : ℝ, K ≤ κbar →
          ∀ (Asel Vsel : ℝ → ℝ) (qN qA : ℝ),
            IsBenchEq pa c r 1 Asel qN → IsABEq pa c r 1 κbar Asel Vsel qA →
            csNA r 1 qN (Asel qN) < csAB r 1 κbar qA (Asel qA) (Vsel qA)) ∧
      (r ≤ (Real.sqrt 141 - 1) / 14 →
        ∃ K : ℝ, 0 < K ∧ ∀ κbar : ℝ, K ≤ κbar →
          ∀ (Asel Vsel : ℝ → ℝ) (qN qA : ℝ),
            IsBenchEq pa c r 1 Asel qN → IsABEq pa c r 1 κbar Asel Vsel qA →
            csAB r 1 κbar qA (Asel qA) (Vsel qA) < csNA r 1 qN (Asel qN))) ∧
    (∀ pa c t : ℝ, Standing pa c 1 t →
      (4 / 5 < t →
        ∃ K : ℝ, 0 < K ∧ ∀ κbar : ℝ, K ≤ κbar →
          ∀ (Asel Vsel : ℝ → ℝ) (qN qA : ℝ),
            IsBenchEq pa c 1 t Asel qN → IsABEq pa c 1 t κbar Asel Vsel qA →
            csNA 1 t qN (Asel qN) < csAB 1 t κbar qA (Asel qA) (Vsel qA)) ∧
      (t ≤ 4 / 5 →
        ∃ K : ℝ, 0 < K ∧ ∀ κbar : ℝ, K ≤ κbar →
          ∀ (Asel Vsel : ℝ → ℝ) (qN qA : ℝ),
            IsBenchEq pa c 1 t Asel qN → IsABEq pa c 1 t κbar Asel Vsel qA →
            csAB 1 t κbar qA (Asel qA) (Vsel qA) < csNA 1 t qN (Asel qN))) := by sorry

end AdBlocking.Surplus
