-- Prove2me | Theorems.Thm_AuditWhistle_Intensity_enforcer_best_response
-- name    : AuditWhistle.Intensity.enforcer_best_response
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:28.03341+00:00
-- url     : https://prove2.me/theorems/0df932d6-6f90-44aa-a692-b018ebc4ee6e
-- title:
--   §3.1, p. 12 — the enforcer's optimal efforts e₁, e₀ given the conjectured audit quality, with e₁ > e₀ and e₀ < 1
-- statement:
--   Fix a model with $0<p<1$, $\tfrac12<\beta<1$, positive $R,\gamma,D,k$ and $R/\gamma<1/(1-p)$, an intensity $\tau\in(0,1)$ and a conjectured audit quality $\hat a\in(0,1)$. Let the enforcer's posteriors $\Pr(B\mid g,W_1)$, $\Pr(B\mid g,W_0)$ be computed by Bayes' rule, and call $e\in[0,1]$ a best response at posterior $q$ if it maximizes $qeR-\tfrac12\gamma e^2$ over $[0,1]$. Then:
--
--   1. the best response after a tip is unique and equals
--   $$e_1=\min\Big\{1,\ \frac{R}{\gamma}\,\frac{(1-p)(1-\hat a)\beta}{(1-p)(1-\hat a)\beta+p(1-\beta)}\Big\};$$
--   2. the best response after silence is unique and equals
--   $$e_0=\frac{R}{\gamma}\,\frac{(1-p)(1-\hat a)(1-\beta\tau)}{(1-p)(1-\hat a)(1-\beta\tau)+p\,[1-(1-\beta)\tau]};$$
--   3. $e_1>e_0$;
--   4. $\Pr(B\mid g,W_0)<1-p$;
--   5. $e_0<1$.
--
--   These are the enforcer's reaction functions used in the equilibrium of Proposition 1.
--
--   **Formalization Note** Effort is restricted to $[0,1]$, which is where the $\min\{1,\cdot\}$ comes from; no $\min$ is needed for $e_0$ because $R/\gamma<1/(1-p)$ and item 4 give $e_0<1$.
-- source:
--   Nan, Tang & Ye, Auditing with a Chance of Whistleblowing, author manuscript dated December 30, 2024 (Management Science, DOI 10.1287/mnsc.2024.04808), p. 12, §3.1, display after (3)

import Mathlib
import Definitions.Def_AuditWhistle_Intensity_Setting

namespace AuditWhistle.Intensity

theorem enforcer_best_response (M : Model) (τ â : ℝ) (hτ : τ ∈ Set.Ioo (0:ℝ) 1)
    (hâ : â ∈ Set.Ioo (0:ℝ) 1) :
    (∀ e : ℝ, IsEnforcerBR M (postW1 M τ â) e ↔
      e = min 1 (M.R / M.γ * ((1 - M.p) * (1 - â) * M.β /
        ((1 - M.p) * (1 - â) * M.β + M.p * (1 - M.β))))) ∧
    (∀ e : ℝ, IsEnforcerBR M (postW0 M τ â) e ↔
      e = M.R / M.γ * ((1 - M.p) * (1 - â) * (1 - M.β * τ) /
        ((1 - M.p) * (1 - â) * (1 - M.β * τ) + M.p * (1 - (1 - M.β) * τ)))) ∧
    (∀ e1 e0 : ℝ, IsEnforcerBR M (postW1 M τ â) e1 → IsEnforcerBR M (postW0 M τ â) e0 →
      e0 < e1) ∧
    postW0 M τ â < 1 - M.p ∧
    (∀ e0 : ℝ, IsEnforcerBR M (postW0 M τ â) e0 → e0 < 1) := by sorry

end AuditWhistle.Intensity
