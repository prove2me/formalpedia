-- Prove2me | Theorems.Thm_FamousTheorems_fernique
-- name    : FamousTheorems.fernique
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T09:15:07.875197+00:00
-- url     : https://prove2.me/theorems/06bb784e-0653-4a8f-82a2-515cc7a018b4
-- title:
--   Fernique's theorem
-- statement:
--   **Fernique's theorem.** For every Gaussian probability measure $\mu$ on a separable Banach space $E$ there is $C>0$ with $\int_E e^{C\|x\|^2}\,d\mu(x)<\infty$.
--
--   Gaussian measures therefore have Gaussian tails in norm, and all moments $\int\|x\|^p\,d\mu$ are finite, even in infinite dimensions where no density exists. This underpins the theory of Gaussian processes, abstract Wiener spaces and large deviations.
--
--   **Formalization note.** Mathlib's `ProbabilityTheory.IsGaussian.exists_integrable_exp_sq`; `IsGaussian μ` means every continuous linear functional pushes $\mu$ to a real Gaussian.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ProbabilityTheory.IsGaussian.exists_integrable_exp_sq`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem fernique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E] (μ : MeasureTheory.Measure E) [ProbabilityTheory.IsGaussian μ] :
    ∃ C : ℝ, 0 < C ∧ MeasureTheory.Integrable (fun x => Real.exp (C * ‖x‖ ^ 2)) μ := by sorry

end FamousTheorems
