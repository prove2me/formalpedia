-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_first_critical_value_identification
-- name    : BirkhoffGlobalSection.first_critical_value_identification
-- status  : Proved
-- author  : @Yivy Yu
-- created : 2026-09-12T15:06:41.557729+00:00
-- url     : https://prove2.me/theorems/9fa13f28-5308-4bec-836f-7f8e59e09446
-- title:
--   Identification of the first critical value
-- statement:
--   Let $0<\mu<1$. The set of collision-free critical values of the Jacobi Hamiltonian is nonempty and bounded below. Its infimum is attained at a collision-free equilibrium $L_1$ lying strictly between the primaries on their common axis:
--
--   $$
--   H_\mu(L_1)=h_1(\mu)=\inf\{H_\mu(s):s\text{ is a collision-free critical point}\}.
--   $$
--
--   This makes the phrase “below the first critical value” a proved geometric threshold rather than reliance on the total behavior of `sInf`.
-- source:
--   Liu--Salomão, Section 4 (the five Lagrange values and L1 as the smallest), https://arxiv.org/abs/2506.17867v2; Joung--van Koert, Section 2.1, https://arxiv.org/abs/2407.19159v3.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- The first collision-free critical value is a genuine minimum and is
attained at the equilibrium between the primaries. -/
theorem first_critical_value_identification (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    (criticalValueSet μ).Nonempty ∧
    BddBelow (criticalValueSet μ) ∧
    ∃ l₁ : Phase,
      IsInnerLagrangePoint μ l₁ ∧
      jacobiHamiltonian μ l₁ = firstCriticalValue μ := by sorry

end BirkhoffGlobalSection
