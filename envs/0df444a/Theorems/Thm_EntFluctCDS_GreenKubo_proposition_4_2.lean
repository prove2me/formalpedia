-- Prove2me | Theorems.Thm_EntFluctCDS_GreenKubo_proposition_4_2
-- name    : EntFluctCDS.GreenKubo.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:33.03462+00:00
-- url     : https://prove2.me/theorems/ada554d1-ac32-4246-a6d6-fd6232a584ed
-- title:
--   Proposition 4.2 — finite-time generalized Evans–Searles identity
-- statement:
--   Let $(M,\phi_X,\omega_X,\Phi_X)$ be a regular force family satisfying (T1) and (T2), and let $P_X^t$ be the law under $\omega_X$ of the time-averaged flux $t^{-1}\int_0^t\Phi_X\circ\phi_X^s\,ds$. For any force $X$ and nonzero time $t$, its reflection $\bar P_X^t$ is equivalent to $P_X^t$, with
--
--   $$\frac{d\bar P_X^t}{dP_X^t}(s)=\exp(-tX\cdot s)\quad P_X^t\text{-almost everywhere}. $$
--
--   This is the measure form of the finite-time generalized Evans–Searles relation; it links the probabilities of opposite flux values.
--
--   **Formalization Note** The paper writes “any $t$”, but $\Sigma_X^0$ contains division by zero and is undefined. The statement explicitly requires $t\ne0$.
-- source:
--   Jakšić, Pillet & Rey-Bellet, Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems, arXiv:1009.3248v2, p. 19, Proposition 4.2, (4.27)

import Mathlib
import Definitions.Def_EntFluctCDS_GreenKubo_Family

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace EntFluctCDS.GreenKubo

/-- Proposition 4.2, p. 19, at nonzero time, where Σ_X^t is defined. -/
theorem proposition_4_2 {N : ℕ} {M : Type*} [MeasurableSpace M]
    (F : Family N M) (hT1 : T1 F) (hT2 : T2 F)
    (X : Fin N → ℝ) (t : ℝ) (ht : t ≠ 0) :
    reflectedFluxLaw F X t ≪ fluxLaw F X t ∧
    fluxLaw F X t ≪ reflectedFluxLaw F X t ∧
    ∀ᵐ s ∂(fluxLaw F X t),
      (reflectedFluxLaw F X t).rnDeriv (fluxLaw F X t) s =
        ENNReal.ofReal (Real.exp (-t * ∑ j, X j * s j)) := by sorry

end EntFluctCDS.GreenKubo
