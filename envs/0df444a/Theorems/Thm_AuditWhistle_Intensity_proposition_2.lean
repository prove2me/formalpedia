-- Prove2me | Theorems.Thm_AuditWhistle_Intensity_proposition_2
-- name    : AuditWhistle.Intensity.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:34.040653+00:00
-- url     : https://prove2.me/theorems/bd44d8e2-2ce5-46b3-83bc-6aafb56410b6
-- title:
--   Proposition 2, p. 13 — increasing whistleblowing intensity lowers equilibrium audit quality if and only if R/γ > r* and D/k < d*
-- statement:
--   Fix real numbers $p,\beta,r$ and an intensity $\tau\in(0,1)$. There is a threshold $d^*$, depending only on $(p,\beta,r,\tau)$, with $d^*>0$ whenever $r>r^*(p,\beta,\tau)$, such that the following holds for **every** model with these $p$ and $\beta$ and with $R/\gamma=r$ (whatever its $D$ and $k$): if $A$ is the equilibrium audit quality as a function of the intensity, i.e. $(A(\tau'),e_1,e_0)$ is an equilibrium for some $e_1,e_0$ at every $\tau'\in(0,1)$, then
--   $$A \text{ is differentiable at } \tau \text{ with } A'(\tau)<0\quad\iff\quad \frac{R}{\gamma}>r^*\ \text{and}\ \frac{D}{k}<d^*,$$
--   where
--   $$r^*=\frac{\beta\,[\tau(\beta-2\beta p+p)-1]^2}{(p-1)(\beta\tau-1)\,[\beta-\beta^2\tau+(2\beta-1)p(\beta\tau+1)]}.$$
--
--   In words: increasing whistleblowing intensity impairs audit quality exactly when the enforcer's incentive $R/\gamma$ is high and the auditor's incentive $D/k$ is low. More whistleblowing makes silence reassuring, so the enforcer investigates less without a tip, and this can outweigh the direct gain in detection.
--
--   **Formalization Note** "Impairs audit quality" is the paper's $da^*/d\tau<0$, stated as the existence of a negative derivative (not via `deriv`, whose junk value $0$ at a kink would be misleading). By Proposition 1 the equilibrium path is unique on $(0,1)$, so quantifying over all paths loses nothing. $r^*$ is the explicit formula of p. 33; $d^*$ is existential but chosen before the model, so it does not depend on $D$ or $k$ (it may depend on $p,\beta,r,\tau$, as on p. 33). The clause $d^*>0$ when $r>r^*$ records that the impairing region is nonempty, which the proof supports (as $d\to0$, $a^*\to0<a_1$).
-- source:
--   Nan, Tang & Ye, Auditing with a Chance of Whistleblowing, author manuscript dated December 30, 2024 (Management Science, DOI 10.1287/mnsc.2024.04808), p. 13, Proposition 2 (proof pp. 31–34)

import Mathlib
import Definitions.Def_AuditWhistle_Intensity_Setting

namespace AuditWhistle.Intensity

theorem proposition_2 (p β r τ : ℝ) (hτ : τ ∈ Set.Ioo (0:ℝ) 1) :
    ∃ dStar : ℝ, (rStar p β τ < r → 0 < dStar) ∧
      ∀ M : Model, M.p = p → M.β = β → M.R / M.γ = r →
        ∀ A : ℝ → ℝ, IsEquilibriumPath M A →
          ((∃ v : ℝ, HasDerivAt A v τ ∧ v < 0) ↔ (rStar p β τ < r ∧ M.D / M.k < dStar)) := by sorry

end AuditWhistle.Intensity
