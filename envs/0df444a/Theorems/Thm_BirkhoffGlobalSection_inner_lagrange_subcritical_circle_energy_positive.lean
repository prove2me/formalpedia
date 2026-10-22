-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_subcritical_circle_energy_positive
-- name    : BirkhoffGlobalSection.inner_lagrange_subcritical_circle_energy_positive
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T10:15:33.070985+00:00
-- url     : https://prove2.me/theorems/79d1318d-ba13-463b-b168-1e8af47f97e7
-- title:
--   Positive subcritical energy on the inner Lagrange circle
-- statement:
--   At a Jacobi energy below the first critical value, the regularized Hamiltonian is strictly positive at every phase state whose physical position lies on the circle centered at the left primary and passing through the inner collinear equilibrium. This circle has radius $0<r<1$. The lower bound is uniform in the momentum coordinates because the completed-square terms are nonnegative.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4 and equation (2.2), circle through L1.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem inner_lagrange_subcritical_circle_energy_positive (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ s : Phase,
        ((leviCivitaPosition μ s) 0 + μ) ^ 2 +
          ((leviCivitaPosition μ s) 1) ^ 2 = r ^ 2 →
          0 < leviCivitaHamiltonian μ c s := by sorry

end BirkhoffGlobalSection
