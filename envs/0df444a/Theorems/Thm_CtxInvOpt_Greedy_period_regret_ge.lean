-- Prove2me | Theorems.Thm_CtxInvOpt_Greedy_period_regret_ge
-- name    : CtxInvOpt.Greedy.period_regret_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:01.75876+00:00
-- url     : https://prove2.me/theorems/19a7fdf2-d614-4ee5-a7f4-02111e475cc1
-- title:
--   App-10–App-11, proof of Theorem 2, Step 3 — in every period the greedy policy's regret is at least sin ᾱ / 4
-- statement:
--   In the instance of Step 2 (dimension $3$, $C_0=C_{0,\bar\alpha}$, $c^\star=(\cos\bar\alpha,\sin\bar\alpha,0)$, $f_t=\mathrm{id}$, $\mathcal X_t=\{\bar x_t,0\}$, horizon $T\ge1$), assume $0<\bar\alpha<\pi/2$ and $\tan\bar\alpha\le2$. Then every run of the greedy circumcenter policy has, in each period $t=1,\dots,T$,
--
--   $$\big(x^\pi_t-x^\star_t\big)'c^\star\ \ge\ \frac{\sin\bar\alpha}{4}.$$
--
--   Summing over the $T$ periods gives cumulative regret at least $T\sin\bar\alpha/4$, linear in the horizon.
--
--   **Formalization Note** The proof's "$\varepsilon^2\le1$" holds for all $\varepsilon_t\le\tan\bar\alpha/2$ only when $\tan\bar\alpha\le2$, which is therefore a hypothesis (the theorem uses $\bar\alpha=\pi/4$). Periods are $0$-based: the claim is for Lean periods $t<T$. Contexts are the identity, so $f_t(x^\pi_t)-f_t(x^\star_t)=x^\pi_t-x^\star_t$.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, App-10–App-11, proof of Theorem 2, Step 3

import Mathlib
import Definitions.Def_CtxInvOpt_Offline_Geometry
import Definitions.Def_CtxInvOpt_Greedy_Online
import Definitions.Def_CtxInvOpt_Greedy_Policy
import Definitions.Def_CtxInvOpt_Greedy_Family

open Real

namespace CtxInvOpt.Greedy

/-- **arXiv:2106.14015v3, App-10–App-11, proof of Theorem 2, Step 3.** In the instance of Step 2,
with `tan ᾱ ≤ 2` (the page's "`ε² ≤ 1`"), every run of the greedy circumcenter policy incurs regret
at least `sin ᾱ / 4` in every period `t < T` (0-based). -/
theorem period_regret_ge {a : ℝ} (ha0 : 0 < a) (ha1 : a < π / 2) (htan : Real.tan a ≤ 2)
    {T : ℕ} (hT : 1 ≤ T) {xpi xstar chat : ℕ → EuclideanSpace ℝ (Fin 3)}
    (hrun : IsGreedyRun (Cfam 0 a) (cstarFam a) (instX a T) (fun _ => id) xpi xstar chat) :
    ∀ t < T, Real.sin a / 4 ≤ inner ℝ (xpi t - xstar t) (cstarFam a) := by sorry

end CtxInvOpt.Greedy
