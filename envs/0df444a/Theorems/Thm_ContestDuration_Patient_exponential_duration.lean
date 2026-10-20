-- Prove2me | Theorems.Thm_ContestDuration_Patient_exponential_duration
-- name    : ContestDuration.Patient.exponential_duration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:51.642289+00:00
-- url     : https://prove2.me/theorems/52e56977-3a1f-4137-9a11-e15a25eeb837
-- title:
--   Proof of Theorem 1(b) — duration under exponential productivity
-- statement:
--   Suppose per-time productivity is $\theta(t)=e^{\rho t}$ with $\rho\ne0$. In the patient regime, if $T$ is the organizer's optimal feasible duration and the logarithm's argument is positive, then
--
--   $$T=\frac{b-1}{b\rho}\log\left(1+\frac{b\rho}{b-1}\frac{A-NF}{cN}\left(\frac{Ax}{cb}\right)^{-b/(b-1)}\right).$$
--
--   This is the closed expression for $\bar T$ used in the paper's analysis of productivity growth.
--
--   **Formalization Note** The positive logarithm argument is explicit. For sufficiently negative $\rho$, equation (9) has no positive solution and the closed expression has no duration meaning.
-- source:
--   Korpeoglu, Körpeoğlu & Tunç, Optimal Duration of Innovation Contests, SSRN 3064763 (authors' version, forthcoming at M&SOM; PDF of 2020-07-23), p. 27, proof of Theorem 1(b), formula for T* = T̄

import Mathlib
import Definitions.Def_ContestDuration_Patient_Model

namespace ContestDuration.Patient

theorem exponential_duration (P : Params) (hS : P.Standing) (h : ℝ → ℝ)
    (hh : ShockOK h) (hx : 0 < xOf P h) (ρ : ℝ) (hρ : ρ ≠ 0)
    (hR : RegularProfit P (fun t => Real.exp (ρ * t)) h)
    (hP : IsPatient P (fun t => Real.exp (ρ * t)) h)
    (hlog : 0 < P.b * ρ / (P.b - 1) * Kbar P h + 1)
    (T : ℝ) (hT : IsOptDuration P (fun t => Real.exp (ρ * t)) h T) :
    T = (P.b - 1) / (P.b * ρ) *
      Real.log (P.b * ρ / (P.b - 1) * Kbar P h + 1) := by sorry

end ContestDuration.Patient
