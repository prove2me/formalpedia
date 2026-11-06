-- Prove2me | Theorems.Thm_BianchiIX_stableResidual_coefficients_bound
-- name    : BianchiIX.stableResidual_coefficients_bound
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T15:10:38.53122+00:00
-- url     : https://prove2.me/theorems/165c36ea-1a7a-4e95-82e7-d3700fe534a5
-- title:
--   All four corrected-phase residual coefficients have the same inverse phase bound
-- statement:
--   Set $r=\sqrt{(m+1)^2+w^2}$ and
--   $$A(m)=\frac{m}{m^2-1},\quad C(m)=-\frac2{m+1},\quad
--   \Theta(m,u,w)=r-1+A(m)u^2+C(m)uw.$$
--   Its explicit gradient is used together with the residual
--   $R=r_4u^4+r_3u^3w+r_2u^2w^2+r_1uw^3$, where
--   $$r_4=-\frac{2m}{(m^2-1)^2},\quad r_3=\frac{2(3m-1)}{(m^2-1)^2},$$
--   $$r_2=-\frac{m^2+1}{(m^2-1)^2}-\frac m{m^2-1}
--   +\frac{r+1}{r(r+m+1)},\quad
--   r_1=\frac2{(m+1)^2}+\frac1{m+1}-\frac1{r+m+1}.$$
--   For $m\geq3/2$ and any real $w$,
--   $$|r_4(m)|,|r_3(m)|,|r_2(m,w)|,|r_1(m,w)|\leq64/(m+1).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/StableResidualBounds.lean#L7-L88

import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
open BianchiIX

theorem BianchiIX.stableResidual_coefficients_bound {m w : ℝ} (hm : 3 / 2 ≤ m) :
    |stableResidual4 m| ≤ 64 / (m + 1) ∧ |stableResidual3 m| ≤ 64 / (m + 1) ∧
    |stableResidual2 m w| ≤ 64 / (m + 1) ∧ |stableResidual1 m w| ≤ 64 / (m + 1) := by sorry
