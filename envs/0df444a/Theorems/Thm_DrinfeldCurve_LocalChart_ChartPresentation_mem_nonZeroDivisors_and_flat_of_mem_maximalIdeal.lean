-- Prove2me | Theorems.Thm_DrinfeldCurve_LocalChart_ChartPresentation_mem_nonZeroDivisors_and_flat_of_mem_maximalIdeal
-- name    : DrinfeldCurve.LocalChart.ChartPresentation.mem_nonZeroDivisors_and_flat_of_mem_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/e260246a-28e5-5c10-9133-a07d16cf06a0
-- title:
--   Flatness and non-zero-divisors in a Drinfeld chart ring
-- statement:
--   Let $q$ be a prime, let $O$ be a discrete valuation ring which is a domain, and let $\varpi \in O$ be a nonzero element of the maximal ideal of $O$. Let $\mathrm{pr}$ be a chart presentation over $O$ at $\varpi$, that is, a triple of formal power series $f, u, v \in O[\![X_0, X_1]\!]$ with $u$ and $v$ units and with $f - (X_0X_1^q - X_0^qX_1) \in (X_0, X_1)^{q+2}$, and write $g = C(\varpi^{q+1})\,v - f u$ for the associated relation and $S = O[\![X_0, X_1]\!]/(g)$ for the associated chart ring. The assertion is the conjunction of four statements: for every $a \in O$ with $a \neq 0$, the image in $S$ of the constant power series $C(a)$ is a non-zero-divisor; $S$ is flat as an $O$-module; the image of $X_0$ in $S$ is a non-zero-divisor; and the image of $X_1$ in $S$ is a non-zero-divisor.
--
--   This is the basic integrality statement for the Katz–Mazur style local chart ring attached to the Drinfeld form $X_0X_1^q - X_0^qX_1$, with an arbitrary nonzero parameter $\varpi$ in the maximal ideal rather than a uniformiser; over a discrete valuation ring flatness amounts to torsion-freeness. It is what allows the blow-up charts obtained by adjoining $X_0/\varpi, X_1/\varpi$ or $\varpi/X_0, X_1/X_0$ to be formed inside genuine localisations, and it is used in the identification of the completions of those charts at suitable maximal ideals with powers of the $uv$-crossing model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DrinfeldCurve_LocalChart_ChartPresentation_mem_nonZeroDivisors_and_flat_of_mem_maximalIdeal.lean

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPowerSeries IsLocalRing DrinfeldCurve DrinfeldCurve.LocalChart

theorem DrinfeldCurve.LocalChart.ChartPresentation.mem_nonZeroDivisors_and_flat_of_mem_maximalIdeal
    (q : ℕ) [Fact q.Prime]
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ϖ : O) (hϖ : ϖ ∈ maximalIdeal O) (hϖ0 : ϖ ≠ 0)
    (pr : ChartPresentation q O ϖ) :
    (∀ a : O, a ≠ 0 → Ideal.Quotient.mk (Ideal.span {pr.rel}) (C a) ∈ nonZeroDivisors pr.Ring) ∧
    Module.Flat O pr.Ring ∧
    Ideal.Quotient.mk (Ideal.span {pr.rel}) (X 0) ∈ nonZeroDivisors pr.Ring ∧
    Ideal.Quotient.mk (Ideal.span {pr.rel}) (X 1) ∈ nonZeroDivisors pr.Ring := by sorry
