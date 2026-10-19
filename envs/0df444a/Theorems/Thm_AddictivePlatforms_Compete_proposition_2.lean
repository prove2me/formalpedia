-- Prove2me | Theorems.Thm_AddictivePlatforms_Compete_proposition_2
-- name    : AddictivePlatforms.Compete.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T12:58:21.979839+00:00
-- url     : https://prove2.me/theorems/4f26bfb9-a594-4bbb-b333-24f8438c0760
-- title:
--   Proposition 2, p. 11 — for K ≥ 2 the unique equilibrium has every platform at the d* > 0 solving (3)
-- statement:
--   Assume Assumptions 1–2 (with the mission's standing pins), let $K \ge 2$ platforms compete and let the cap satisfy $\overline{A} > 0$. Then there is $d^* > 0$ satisfying the indifference condition
--   $$K \cdot u\!\left(\frac{A_K(d^*)}{K}, d^*\right) - C(A_K(d^*)) = (K-1)\cdot u\!\left(\frac{A_{K-1}(d^*)}{K-1}, d^*\right) - C(A_{K-1}(d^*)), \qquad (3)$$
--   such that
--   1. the profile in which every platform chooses $d^*$ is the platform profile of a pure-strategy subgame perfect equilibrium, and
--   2. in every pure-strategy subgame perfect equilibrium every platform chooses $d^*$.
--
--   Competition thus pushes each platform's addictiveness up to the point where the consumer is just indifferent between keeping and dropping it, and this addictiveness is strictly positive.
--
--   **Formalization Note.** Uniqueness concerns the platforms' profile; the consumer's off-path choices are part of the strategy and need not be unique. An equilibrium requires the consumer to best-respond at every profile, on and off the path. $\overline{A} > 0$ is a disclosed pin: at $\overline{A} = 0$ every profile is an equilibrium. Equation (3) is stated through maximizers as in Step 1. The existence pin for $K$ platforms is assumed.
-- source:
--   Ichihashi & Kim, Addictive Platforms, Bank of Canada SWP 2022-16 (Apr. 1, 2022), p. 11, Proposition 2 and (3); proof Appendix B, pp. 31–33

import Mathlib
import Definitions.Def_AddictivePlatforms_Compete_Model

open Set Filter Topology
open scoped ENNReal

namespace AddictivePlatforms.Compete

/-- Proposition 2 (p. 11): for `K ≥ 2` (and `Ā > 0`) there is a `d* > 0` satisfying (3) such that
the profile in which every platform chooses `d*` is supported by an equilibrium, and in every
equilibrium every platform chooses `d*`. -/
theorem proposition_2 (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C) (K : ℕ) (hK : 2 ≤ K)
    (hE : UncOptExists u C K) (Abar : ℝ≥0∞) (hAbar : 0 < Abar) :
    ∃ dstar : ℝ, 0 < dstar ∧ Eq3 u C Abar K dstar ∧
      (∃ σ : ConsumerStrategy K, IsSPE u C Abar (fun _ : Fin K => dstar) σ) ∧
      ∀ (d : Fin K → ℝ) (σ : ConsumerStrategy K), IsSPE u C Abar d σ → ∀ k, d k = dstar := by sorry

end AddictivePlatforms.Compete
