-- Prove2me | Theorems.Thm_ContestDuration_Patient_theorem_1
-- name    : ContestDuration.Patient.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:39.247432+00:00
-- url     : https://prove2.me/theorems/12f7ac65-e2ac-4a3c-b1a3-bd516435f792
-- title:
--   Theorem 1 — patient duration rises with uncertainty scale and falls with productivity growth
-- statement:
--   Fix a contest with at least two agents, a given award scheme, and a mean-zero log-concave shock density $h$ with positive marginal incentive $x$. For every positive uncertainty scale $\alpha$ in the patient regime, the organizer has a unique optimal feasible duration $T^*(\alpha)$. For any two such scales,
--
--   $$0<\alpha_1<\alpha_2\quad\Longrightarrow\quad T^*(\alpha_1)<T^*(\alpha_2).$$
--
--   When productivity has the form $\theta(t)=e^{\rho t}$ and the uncertainty scale is normalized to one, every productivity exponent $\rho$ in the patient regime likewise has a unique optimal feasible duration. For any two such exponents,
--
--   $$\rho_1<\rho_2\quad\Longrightarrow\quad T^*(\rho_2)<T^*(\rho_1).$$
--
--   This is the paper's comparison of contest length with agent uncertainty and changing productivity when the organizer's discount factor is below the threshold $\delta_1$.
--
--   **Formalization Note** The award scheme is fixed; only duration is optimized. The patient threshold is recomputed from the scaled density or the selected productivity, and the two comparison points must each satisfy the regime assumptions. Positive $x$, a positive solution to equation (9), and an agent best response at that solution are explicit conditions. The optimum maximizes profit subject to the agent best-response and participation constraints, rather than being defined by equation (9).
-- source:
--   Korpeoglu, Körpeoğlu & Tunç, Optimal Duration of Innovation Contests, SSRN 3064763 (authors' version, forthcoming at M&SOM; PDF of 2020-07-23), p. 14, Theorem 1(a)–(b); p. 27, proof of Theorem 1

import Mathlib
import Definitions.Def_ContestDuration_Patient_Model

namespace ContestDuration.Patient

theorem theorem_1 (P : Params) (hS : P.Standing) (h : ℝ → ℝ)
    (hh : ShockOK h) (hx : 0 < xOf P h) :
    (∀ θ : ℝ → ℝ, ProductivityOK θ →
      (∀ α, 0 < α → RegularProfit P θ (scaled h α) →
        IsPatient P θ (scaled h α) → ∃! T, IsOptDuration P θ (scaled h α) T) ∧
      (∀ α₁ α₂ T₁ T₂, 0 < α₁ → α₁ < α₂ →
        RegularProfit P θ (scaled h α₁) → IsPatient P θ (scaled h α₁) →
        RegularProfit P θ (scaled h α₂) → IsPatient P θ (scaled h α₂) →
        IsOptDuration P θ (scaled h α₁) T₁ →
        IsOptDuration P θ (scaled h α₂) T₂ → T₁ < T₂)) ∧
    ((∀ ρ, RegularProfit P (fun t => Real.exp (ρ * t)) h →
      IsPatient P (fun t => Real.exp (ρ * t)) h →
      ∃! T, IsOptDuration P (fun t => Real.exp (ρ * t)) h T) ∧
    (∀ ρ₁ ρ₂ T₁ T₂, ρ₁ < ρ₂ →
      RegularProfit P (fun t => Real.exp (ρ₁ * t)) h →
      IsPatient P (fun t => Real.exp (ρ₁ * t)) h →
      RegularProfit P (fun t => Real.exp (ρ₂ * t)) h →
      IsPatient P (fun t => Real.exp (ρ₂ * t)) h →
      IsOptDuration P (fun t => Real.exp (ρ₁ * t)) h T₁ →
      IsOptDuration P (fun t => Real.exp (ρ₂ * t)) h T₂ → T₂ < T₁)) := by sorry

end ContestDuration.Patient
