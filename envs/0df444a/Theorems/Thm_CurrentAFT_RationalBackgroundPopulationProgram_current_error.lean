-- Prove2me | Theorems.Thm_CurrentAFT_RationalBackgroundPopulationProgram_current_error
-- name    : CurrentAFT.RationalBackgroundPopulationProgram.current_error
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T18:36:40.912813+00:00
-- url     : https://prove2.me/theorems/51f6c0de-9945-4c12-a67c-22685eb11b21
-- title:
--   Numerical error of the fixed-queue background population program
-- statement:
--   Let $\lambda,B,R\in\mathbb N$, with $R\ge 2$, and let $a\in\mathbb Z$ be the fixed queue value. Write $L=\mathrm{Parameters.base}(\lambda)$, $d=\mathrm{Parameters.dimension}(\lambda)$, $q=\mathrm{Parameters.modulus}(\lambda)$ and $\varepsilon=2^{-B}$. Assume the program's predicate $\mathrm{PrecisionBudget}(\lambda,B)$ and the two inequalities
--   $$\varepsilon\le\frac1{4L},\qquad 64Ld\varepsilon\le\frac1{4q}.$$
--   For every admissible truncated arity $u$ of order $R$, every color tuple in the first-histogram palette, and every center tuple in the safe palette, the rational background population program approximates the corresponding exact fixed-queue background coefficient:
--   $$\left|\operatorname{current}(\lambda,B,R,a,u,\mathrm{colors},\mathrm{centers})-\operatorname{fixedQueueBackground}(\lambda,R,a,u)(\mathrm{colors},\mathrm{centers})\right|\le E_{\mathrm{bg}}(\lambda,R)\varepsilon.$$
--   Here $E_{\mathrm{bg}}$ is the explicit function `RationalBackgroundPopulationProgram.errorConstant`; the rational output is viewed in $\mathbb R$. The estimate is uniform over the displayed palette tuples and supplies the background contribution to the numerical response error.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/CurrentAFT/RationalBackgroundPopulationProgram.lean, lines 154-185. Exact native theorem type with the complete oracle-selected proof dependency cluster. Source SHA256 b5a028201d3ac239ff43e3fbfd1a650756dffa680b4e6d1ee2bce6ff61f59b0c.

import Definitions.Def_InfoLossLAR_NativeBundle_09

















section




/-! # The three actual population products of the original fixed-queue background -/
namespace CurrentAFT.RationalBackgroundPopulationProgram
open AFT GradedControlAlgebra ActualControls BackgroundFamilies BackgroundScalarZero
open RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
  PublicParameterProgram.modulus ProposalPrimary.primaryLaw bodyReference
  RationalBackgroundProgram.free RationalBackgroundProgram.translation RationalLegBackgroundProgram.current
  RationalFamilyProductProgram.binomial RationalFamilyProductProgram.product







noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.RationalBackgroundPopulationProgram.populationFinDecidableEq





























set_option maxRecDepth 8192

theorem _root_.CurrentAFT.RationalBackgroundPopulationProgram.current_error (security bits order : ℕ) (horder : 2≤order) (queue : ℤ)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(current security bits order queue arity (fun index => (colors index).val) (fun index => (centers index).val.val):ℝ)-
      (ActualBackground.fixedQueueBackground security order horder queue arity).val colors centers| ≤
      errorConstant security order*(1/(2:ℝ)^bits) := by sorry
