-- Prove2me | Theorems.Thm_AuditWhistle_Intensity_astar_strictMono_d
-- name    : AuditWhistle.Intensity.astar_strictMono_d
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:42.787913+00:00
-- url     : https://prove2.me/theorems/aca31691-442e-4075-bbde-fba75fe4285d
-- title:
--   Appendix, proof of Proposition 2, p. 33 — equilibrium audit quality a* increases with d = D/k, giving a threshold d*
-- statement:
--   1. Let two models share $p$, $\beta$ and $R/\gamma$, and have $D/k<D'/k'$. If at the same $\tau\in(0,1)$ the first has an equilibrium with audit quality $a$ and the second an equilibrium with audit quality $a'$, then $a<a'$.
--   2. For all $p,\beta,r$, $\tau\in(0,1)$ and every level $a_1$, there is a threshold $d^*$ such that, for every model with these $p$, $\beta$ and $R/\gamma=r$ and every equilibrium $(a,e_1,e_0)$ of it at $\tau$,
--   $$a<a_1\iff \frac{D}{k}<d^*.$$
--
--   This is the step of the proof of Proposition 2 that turns the threshold $a_1$ on audit quality into the threshold $d^*$ on the auditor's incentive.
--
--   **Formalization Note** The paper's reason, $\partial V/\partial d<0$, is not stated; the claim "a* increase with d" is stated by comparing equilibria of two models, which needs no derivative. In part 2, $d^*$ is chosen before the model, so it does not depend on $D$ or $k$.
-- source:
--   Nan, Tang & Ye, Auditing with a Chance of Whistleblowing, author manuscript dated December 30, 2024 (Management Science, DOI 10.1287/mnsc.2024.04808), p. 33, Appendix, proof of Proposition 2

import Mathlib
import Definitions.Def_AuditWhistle_Intensity_Setting

namespace AuditWhistle.Intensity

theorem astar_strictMono_d :
    (∀ (M M' : Model) (τ a e1 e0 a' e1' e0' : ℝ), M.p = M'.p → M.β = M'.β →
      M.R / M.γ = M'.R / M'.γ → M.D / M.k < M'.D / M'.k → τ ∈ Set.Ioo (0:ℝ) 1 →
      IsEquilibrium M τ a e1 e0 → IsEquilibrium M' τ a' e1' e0' → a < a') ∧
    (∀ p β r τ a1 : ℝ, τ ∈ Set.Ioo (0:ℝ) 1 →
      ∃ dStar : ℝ, ∀ M : Model, M.p = p → M.β = β → M.R / M.γ = r →
        ∀ a e1 e0 : ℝ, IsEquilibrium M τ a e1 e0 → (a < a1 ↔ M.D / M.k < dStar)) := by sorry

end AuditWhistle.Intensity
