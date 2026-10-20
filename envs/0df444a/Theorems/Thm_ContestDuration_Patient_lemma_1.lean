-- Prove2me | Theorems.Thm_ContestDuration_Patient_lemma_1
-- name    : ContestDuration.Patient.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:37.584993+00:00
-- url     : https://prove2.me/theorems/9c0cee0d-d3dd-451c-8a5a-94e46c027bbf
-- title:
--   Lemma 1 — optimal allocation and effort cost
-- statement:
--   Let productivity $\theta(t)$ be continuous and positive for $t\ge0$, let $b>1$ and $c>0$, and let an agent provide total deterministic effort $e\ge0$ over a duration $T>0$. The per-time allocation $\eta^*(t)=e\theta(t)^{1/(b-1)}/\tau(T)$ achieves total effort $e$ and has cost
--
--   $$\int_0^T c\eta^*(t)^b\,dt=\psi(e,T)=c e^b\tau(T)^{1-b}.$$
--
--   Every nonnegative per-time allocation with total effort $e$ and integrable output and cost has cost at least $\psi(e,T)$. For fixed positive duration this cost is increasing and convex in $e\ge0$; for fixed $e>0$ it decreases with duration.
--
--   This reduction lets the remaining contest model use total effort instead of a full time path.
--
--   **Formalization Note** The duration and effort domains exclude the zero-duration real-power default and the zero-effort exception to strict decrease in duration. Integrability of competing allocations prevents a nonintegrable Lean integral from evaluating to zero.
-- source:
--   Korpeoglu, Körpeoğlu & Tunç, Optimal Duration of Innovation Contests, SSRN 3064763 (authors' version, forthcoming at M&SOM; PDF of 2020-07-23), p. 10, Lemma 1; p. 26, proof of Lemma 1 and equation (11)

import Mathlib
import Definitions.Def_ContestDuration_Patient_Model

open MeasureTheory

namespace ContestDuration.Patient

theorem lemma_1 (P : Params) (hS : P.Standing) (θ : ℝ → ℝ)
    (hθ : ProductivityOK θ) (e T : ℝ) (he : 0 ≤ e) (hT : 0 < T) :
    totalEffort θ (allocation P.b θ e T) T = e ∧
    allocationCost P.c P.b (allocation P.b θ e T) T = psi P θ e T ∧
    (∀ η : ℝ → ℝ,
      (∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ η t) →
      IntervalIntegrable (fun t => θ t * η t) volume 0 T →
      IntervalIntegrable (fun t => η t ^ P.b) volume 0 T →
      totalEffort θ η T = e → psi P θ e T ≤ allocationCost P.c P.b η T) ∧
    StrictMonoOn (fun z => psi P θ z T) (Set.Ici 0) ∧
    ConvexOn ℝ (Set.Ici 0) (fun z => psi P θ z T) ∧
    (0 < e → StrictAntiOn (fun t => psi P θ e t) (Set.Ioi 0)) := by sorry

end ContestDuration.Patient
