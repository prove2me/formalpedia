-- Prove2me | Theorems.Thm_ClimateImpact_Interaction_prop2_integration_by_parts
-- name    : ClimateImpact.Interaction.prop2_integration_by_parts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:05.723853+00:00
-- url     : https://prove2.me/theorems/4b645b8a-5b16-4717-af6b-56491d69f702
-- title:
--   (39), §6.2, proof of Proposition 2, p. 64 — integration by parts: J̃^i = ∫₀^T ((e^{−ρt}−e^{−ρT})/ρ θ^{c,i}_t + α(1−e^{−ρt})/ρ θ^i_t + c^i_t(1−e^{−ρT})/ρ ψ^i_t) dt
-- statement:
--   Let $\rho>0$ and $T>0$, let company $i$'s cost $s\mapsto c^i_s$ and the risk term $s\mapsto[\Sigma_s\mathbf 1]_i$ be integrable on $[0,T]$, and let $\psi$ be an admissible schedule for company $i$ (nonnegative, with $c^i\psi^i$, $\theta^i(\psi)$ and $\theta^{c,i}(\psi)$ integrable on $[0,T]$). Then:
--
--   1. the reduced objective equals
--   $$\tilde{\mathcal J}^i(\psi)=\int_0^T\Big(\frac{e^{-\rho t}-e^{-\rho T}}{\rho}\,\theta^{c,i}_t(\psi_t)+\alpha\frac{1-e^{-\rho t}}{\rho}\,\theta^i_t(\psi_t)+c^i_t\frac{1-e^{-\rho T}}{\rho}\,\psi^i_t\Big)dt ;$$
--   2. the difference $\mathcal J^i(\psi)-\tilde{\mathcal J}^i(\psi)$ is the same for every admissible schedule $\psi$; in particular maximizing $\mathcal J^i$ over company $i$'s schedule is equivalent to maximizing $\tilde{\mathcal J}^i$.
--
--   This is the step of the proof of Proposition 2 that turns the companies' dynamic problem into the maximization of a time integral of date-$t$ payoffs.
--
--   **Formalization Note** $\rho>0$ is the standing reading of a rate of time preference (the identity divides by $\rho$). Integrability of the data and admissibility are not on the page; they make the integrals well defined. The parameter $\alpha$ is unrestricted here.
-- source:
--   SSRN 3562534 (25 Jun 2021), §6.2, proof of Proposition 2, (39), p. 64

import Mathlib
import Definitions.Def_ClimateImpact_Interaction_TimeFactors
import Definitions.Def_ClimateImpact_Interaction_Objective

open MeasureTheory

namespace ClimateImpact.Interaction

theorem prop2_integration_by_parts {n : ℕ} (ρ T α γstar : ℝ) (hρ : 0 < ρ) (hT : 0 < T)
    (θ θc : ℝ → (Fin n → ℝ) → Fin n → ℝ) (c : Fin n → ℝ → ℝ) (d ψb : Fin n → ℝ)
    (Sig : ℝ → Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (hc_int : IntegrableOn (c i) (Set.Icc 0 T))
    (hSig_int : IntegrableOn (fun s => Matrix.mulVec (Sig s) (fun _ => 1) i) (Set.Icc 0 T))
    (ψ : ℝ → Fin n → ℝ) (hψ : IsAdmissible T θ θc c i ψ) :
    reducedObjective ρ T α θ θc c i ψ =
        ∫ t in (0)..T,
          ((Real.exp (-(ρ * t)) - Real.exp (-(ρ * T))) / ρ * θc t (ψ t) i
            + α * ((1 - Real.exp (-(ρ * t))) / ρ) * θ t (ψ t) i
            + c i t * ((1 - Real.exp (-(ρ * T))) / ρ) * ψ t i) ∧
      ∀ φ : ℝ → Fin n → ℝ, IsAdmissible T θ θc c i φ →
        objective ρ T α γstar θ θc c d ψb Sig i ψ - reducedObjective ρ T α θ θc c i ψ
          = objective ρ T α γstar θ θc c d ψb Sig i φ - reducedObjective ρ T α θ θc c i φ := by sorry

end ClimateImpact.Interaction
