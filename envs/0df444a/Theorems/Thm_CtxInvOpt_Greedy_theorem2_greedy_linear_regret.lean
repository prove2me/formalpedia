-- Prove2me | Theorems.Thm_CtxInvOpt_Greedy_theorem2_greedy_linear_regret
-- name    : CtxInvOpt.Greedy.theorem2_greedy_linear_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:07.5191+00:00
-- url     : https://prove2.me/theorems/12ab6181-09bf-4b4b-a9d6-e1240eab087a
-- title:
--   Theorem 2, pp. 13–14 — the greedy circumcenter policy has worst-case regret Ω(T), even from a pointed knowledge set
-- statement:
--   **Theorem 2 (Insufficiency of the greedy circumcenter policy).** There exist knowledge sets $C$ such that the worst-case regret of the greedy circumcenter policy satisfies
--
--   $$\mathcal{WCR}^{\pi_{greedy}}_T(C)=\Omega(T).$$
--
--   Precisely: in dimension $d=3$ and for any action dimension $n\ge1$, there is a closed, nonempty initial knowledge set $C_0\subseteq S^3$ that is **pointed**, $\alpha(C_0)<\pi/2$, and a constant $\kappa>0$ such that for every horizon $T\ge1$ there are a true cost $c^\star\in C_0$, feasible sets $\mathcal X_t\in\mathfrak B$ (nonempty, compact, diameter at most $1$) and $1$-Lipschitz context functions $f_t\in\mathfrak F$ for which
--
--   1. the greedy circumcenter policy can be run (some run exists), and
--   2. every run, with any choice of circumcenter and any tie-breaking, has regret
--   $$R^{\pi_{greedy}}_T(c^\star,\vec{\mathcal X}_T,\vec f_T)=\sum_{t=1}^T\big(f_t(x^\pi_t)-f_t(x^\star_t)\big)'c^\star\ \ge\ \kappa\,T.$$
--
--   So repeatedly applying the offline-optimal circumcenter policy is not enough online: it can keep paying a constant regret per period while learning almost nothing about $c^\star$. This motivates the paper's EllipsoidalCones algorithm.
--
--   **Formalization Note** The worst-case regret (7) is a supremum over $c^\star\in C_0$ and admissible instances; its lower bound $\Omega(T)$ is stated by exhibiting such an instance, with one $C_0$ and one $\kappa$ for every $T$. Pointedness rules out the trivial witness $C_0=S^3$. The nonvacuity clause rules out a statement that holds because no greedy run exists. The proof's construction is in dimension $3$, as is the statement. Periods are $0$-based in Lean.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, pp. 13–14, Theorem 2; (7), p. 9; proof App-9–App-11

import Mathlib
import Definitions.Def_CtxInvOpt_Offline_Geometry
import Definitions.Def_CtxInvOpt_Greedy_Online
import Definitions.Def_CtxInvOpt_Greedy_Policy

open Real

namespace CtxInvOpt.Greedy

/-- **arXiv:2106.14015v3, Theorem 2 (Insufficiency of the greedy circumcenter policy), pp. 13–14;
proof App-9–App-11.** There is a closed, nonempty, pointed (`α(C₀) < π/2`) initial knowledge set
`C₀ ⊆ S³` and a constant `κ > 0` such that, for every horizon `T ≥ 1`, nature has a true cost
`c⋆ ∈ C₀` and admissible instances `(X_t, f_t)` against which the greedy circumcenter policy can be
run, and every such run (every circumcenter choice, every tie-break) has regret at least `κ T`:
`WCR^{π_greedy}_T(C₀) = Ω(T)`. -/
theorem theorem2_greedy_linear_regret {n : ℕ} (hn : 1 ≤ n) :
    ∃ C0 : Set (EuclideanSpace ℝ (Fin 3)), IsClosed C0 ∧ C0 ⊆ CtxInvOpt.Offline.unitSphere 3 ∧ C0.Nonempty ∧
      CtxInvOpt.Offline.uncAngle C0 < π / 2 ∧
      ∃ κ : ℝ, 0 < κ ∧ ∀ T : ℕ, 1 ≤ T →
        ∃ cstar ∈ C0, ∃ (X : ℕ → Set (EuclideanSpace ℝ (Fin n)))
          (f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin 3)),
          (∀ t, CtxInvOpt.Offline.IsActionSet (X t)) ∧ (∀ t, CtxInvOpt.Offline.IsContext (f t)) ∧
          (∃ xpi xstar chat, IsGreedyRun C0 cstar X f xpi xstar chat) ∧
          ∀ xpi xstar chat, IsGreedyRun C0 cstar X f xpi xstar chat →
            κ * (T : ℝ) ≤ cumRegret cstar f xpi xstar T := by sorry

end CtxInvOpt.Greedy
