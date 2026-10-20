-- Prove2me | Theorems.Thm_ContestDuration_Patient_lemma_2_patient
-- name    : ContestDuration.Patient.lemma_2_patient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:35.163534+00:00
-- url     : https://prove2.me/theorems/1bbd6b1e-3491-4a92-8994-81f9c40b7573
-- title:
--   Lemma 2 — patient organizer's optimal duration is the participation limit
-- statement:
--   Fix an award scheme, a mean-zero log-concave shock density, and positive productivity. Suppose the organizer's profit is unimodal with positive right derivative at zero, the marginal incentive $x$ is positive, and a positive duration $\bar T$ solves equation (9). If the discount factor is below the threshold $\delta_1$ defined in the proof of Lemma 2, then
--
--   $$T\text{ is an optimal feasible duration}\quad\Longleftrightarrow\quad T=\bar T.$$
--
--   Thus the agent's participation condition binds for the patient organizer and uniquely determines the duration. This is the patient half of Lemma 2.
--
--   **Formalization Note** Existence of $\bar T$ is stated explicitly because the integral $\tau$ can be bounded when productivity declines exponentially. The best-response condition at $\bar T$ is explicit, as required by footnote 11 on p. 13. The theorem uses positive durations, as required by the cost expression.
-- source:
--   Korpeoglu, Körpeoğlu & Tunç, Optimal Duration of Innovation Contests, SSRN 3064763 (authors' version, forthcoming at M&SOM; PDF of 2020-07-23), p. 13, Lemma 2 and equation (9); pp. 26–27, proof of Lemma 2 and δ1

import Mathlib
import Definitions.Def_ContestDuration_Patient_Model

namespace ContestDuration.Patient

theorem lemma_2_patient (P : Params) (hS : P.Standing) (h : ℝ → ℝ)
    (hh : ShockOK h) (θ : ℝ → ℝ) (hθ : ProductivityOK θ)
    (hx : 0 < xOf P h) (hR : RegularProfit P θ h)
    (Tb : ℝ) (hTb : 0 < Tb) (hK : tau P.b θ Tb = Kbar P h)
    (hδ : P.δ < delta1 P θ h Tb) :
    ∀ T, IsOptDuration P θ h T ↔ T = Tb := by sorry

end ContestDuration.Patient
