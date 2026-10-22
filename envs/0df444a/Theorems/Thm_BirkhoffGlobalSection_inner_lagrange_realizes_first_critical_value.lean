-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_realizes_first_critical_value
-- name    : BirkhoffGlobalSection.inner_lagrange_realizes_first_critical_value
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T18:47:09.23707+00:00
-- url     : https://prove2.me/theorems/fbb07dc2-f996-440c-bd27-0b63cd706b0f
-- title:
--   Inner Lagrange equilibrium realizes the first critical value
-- statement:
--   For each mass parameter $0<\mu<1$, an inner collinear Lagrange equilibrium $L_1$ exists between the primaries, and its Jacobi Hamiltonian value equals the infimum of all collision-free critical values. This identifies the first critical value with the inner neck energy.
-- source:
--   Joung--van Koert, Proposition 2.4 and equation (2.2), https://arxiv.org/abs/2407.19159v3, PDF pp. 6–7; the standard subcritical Hill-region neck argument.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- The inner collinear equilibrium attains the first collision-free critical
value in the physical mass range. -/
theorem inner_lagrange_realizes_first_critical_value (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    ∃ L : Phase, IsInnerLagrangePoint μ L ∧
      jacobiHamiltonian μ L = firstCriticalValue μ := by sorry

end BirkhoffGlobalSection
