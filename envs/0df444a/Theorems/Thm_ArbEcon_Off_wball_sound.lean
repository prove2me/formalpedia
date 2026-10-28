-- Prove2me | Theorems.Thm_ArbEcon_Off_wball_sound
-- name    : ArbEcon.Off.wball_sound
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:48:43.970098+00:00
-- url     : https://prove2.me/theorems/e2132627-7bf4-4bf5-a2eb-d1fcf44847c6
-- title:
--   Affine combination of two complex enclosures
-- statement:
--   Let complex values $A_1,A_2$ have the defined accumulator enclosures $x_1,x_2$
--   at precision $P$. Let $B=(b_r+ib_i)/d$ with integers $b_r,b_i,d$ and $d>0$.
--   If $(r,i,e_r,e_i)=\operatorname{wData}(b_r,b_i,d,x_1,x_2)$ and
--   $W=A_1+(A_2-A_1)B$, then
--   $$|2^P d\operatorname{Re}W-r|\le e_r,\qquad
--   |2^P d\operatorname{Im}W-i|\le e_i.$$
--   This validates the exact affine-combination enclosure.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/EMZetaOfflineSlabCheck.lean#L54-L117

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCore
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlab
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSound
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_Probes_ArbEconomics_Zeta
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Config64
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.IntervalCases
namespace ZetaReflection
end ZetaReflection
namespace ZetaReflection.EMHigh
end ZetaReflection.EMHigh
/-  EMZetaOfflineSlabCheck.lean -- lane offline: the KERNEL checker of a zero-free cell.

    The off-line evaluator run at a center `c = σc + i tc` with `p + 1` accumulators gives, after
    `N - 1` and `N` terms, balls of `S_k = Σ_{n<N} (log n)^k n^(-c)` and of `S_k + (log N)^k N^(-c)`.
    With the exact correction factor `emCorr K c N = (BreN + i BimN)/BD` (`corrDataG`) they give balls
    of the Taylor weights `W_k = S_k + (log N)^k N^(-c) emCorr K c N` of `EMZetaOfflineSlab`.

      * `wData`, `wball_sound`  -- the ball of `W_k`, scaled by `2^P BD`;
      * `sumM`, `sumM_sound`    -- `Σ_{k≥1} ‖W_k‖ rn^k rd^(p-k) (p!/k!)` from above;
      * `checkCell`, `checkCell_sound` -- ONE Boolean check (run by `decide +kernel`) proving
                                   `Σ_{k=1}^p ‖W_k‖ r^k/k! + FN/FD < ‖W_0‖`, `r = rn/rd`, the
                                   hypothesis `hmain` of `zeta_ne_zero_of_cell`.

    conjecture1_proved = False.  Finite interval arithmetic; nothing about RH.
-/


open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

section
namespace ArbEcon
end ArbEcon
open ArbEcon

section
namespace ArbEcon.Off
end ArbEcon.Off
open ArbEcon.Off

/-! ## A. The Taylor weights from the evaluator's partial sums. -/



/-! ## B. The ball of a weight. -/

theorem ArbEcon.Off.wball_sound (P : ℕ) (A1 A2 : ℂ) (x1 x2 : Acc) (h1 : AccOK P A1 x1) (h2 : AccOK P A2 x2)
    (BreN BimN BD : ℤ) (hBD : (0 : ℝ) < BD) (B : ℂ) (hBre : B.re = (BreN : ℝ) / BD)
    (hBim : B.im = (BimN : ℝ) / BD) :
    |(A1 + (A2 - A1) * B).re * 2 ^ P * BD - ((wData BreN BimN BD x1 x2).1 : ℝ)|
        ≤ ((wData BreN BimN BD x1 x2).2.2.1 : ℝ) ∧
    |(A1 + (A2 - A1) * B).im * 2 ^ P * BD - ((wData BreN BimN BD x1 x2).2.1 : ℝ)|
        ≤ ((wData BreN BimN BD x1 x2).2.2.2 : ℝ) := by sorry
