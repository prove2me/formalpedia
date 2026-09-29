-- Prove2me | Theorems.Thm_BanditAlgorithm_pmSignalMeasure_eq_symmetric_perturbation_of_fiber_sum
-- name    : BanditAlgorithm.pmSignalMeasure_eq_symmetric_perturbation_of_fiber_sum
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-05T19:48:16.003021+00:00
-- url     : https://prove2.me/theorems/19441b51-a775-4bc8-ac58-af86e407d810
-- title:
--   Signal laws coincide under a fiber-invisible symmetric perturbation
-- statement:
--   Let a finite partial-monitoring game have signal map $\Phi$. Fix an action $c$, a base outcome distribution $u$, a perturbation direction $q$, and a scale $\Delta$. Assume both symmetric perturbations $u-\Delta q$ and $u+\Delta q$ are probability distributions. If the perturbation is invisible in every signal fiber of action $c$, meaning
--
--   $$
--   \sum_{i:\,\Phi(c,i)=\sigma}q_i=0
--   \qquad\text{for every signal }\sigma,
--   $$
--
--   then action $c$ induces exactly the same signal law under the two perturbed environments:
--
--   $$
--   S_c(u-\Delta q)=S_c(u+\Delta q).
--   $$
--
--   This is the finite signal-law identity used for actions in the neighborhood $N_{ab}$ in the hard-game lower bound for partial monitoring. It isolates the precise consequence of the kernel/fiber condition in equation (37.6).
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), Theorem 37.12, Step 2, printed p. 490; equation (37.6), https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringStochastic
import Mathlib.Data.ENNReal.BigOperators

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BanditAlgorithm

theorem pmSignalMeasure_eq_symmetric_perturbation_of_fiber_sum
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    [DecidableEq 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (c : Fin k)
    (u q : Fin d → ℝ) (Δ : ℝ)
    (hminus : (fun i => u i - Δ * q i) ∈ stdSimplex ℝ (Fin d))
    (hplus : (fun i => u i + Δ * q i) ∈ stdSimplex ℝ (Fin d))
    (hfiber : ∀ σ : 𝕊,
      ∑ i ∈ Finset.univ.filter (fun i => G.Φ c i = σ), q i = 0) :
    pmSignalMeasure G (fun i => u i - Δ * q i) c =
      pmSignalMeasure G (fun i => u i + Δ * q i) c := by sorry
