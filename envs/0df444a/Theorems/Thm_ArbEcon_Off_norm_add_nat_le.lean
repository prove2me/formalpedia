-- Prove2me | Theorems.Thm_ArbEcon_Off_norm_add_nat_le
-- name    : ArbEcon.Off.norm_add_nat_le
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:47:31.32798+00:00
-- url     : https://prove2.me/theorems/12e09a5a-ff71-4ac3-b9dd-d412e5494d5e
-- title:
--   Bounding shifted complex factors from one corner
-- statement:
--   Let $K\in\mathbb N$, $\sigma_c,U\ge0$, $t_c\in\mathbb R$, and suppose
--   $$(\sigma_c+(2K-1))^2+t_c^2\le U^2.$$
--   Then, for every natural $j<2K$,
--   $$|\sigma_c+it_c+j|\le U.$$
--   The expression $2K-1$ is evaluated in the real numbers.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/EMZetaOfflineSlabClear.lean#L33-L49

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCore
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlab
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabClear
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSound
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_EdgeClearGlue
import Definitions.Def_ArdaRH65K_Turing121_Probes_ArbEconomics_Zeta
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Definitions.Def_ArdaRH65K_Turing121_TuringBand
import Definitions.Def_ArdaRH65K_XiLineZeros
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Config64
import Mathlib
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
/-  EMZetaOfflineSlabClear.lean -- lane offline: from kernel-checked cells to an edge-clearance slab
    `EdgeClearGlue.SlabClear a b` (brick K1's numerical input, memo ANDURIL_ARB_DISCHARGE_2026-09-23
    rows H2a/H2c).

      * `cell_zeta_ne_zero` -- ONE cell, packaged: two evaluator invariants at the center
                               `c = σc + i tc` (after `N - 1` and `N` terms, `p + 1` accumulators), the
                               kernel check `checkCell … = true`, and a handful of scalar side
                               conditions (log bracket, `r L ≤ 1`, `‖c + j‖ ≤ U`, the remainder
                               certificate, the error budget) give `ζ(s) ≠ 0` for every `s` with
                               `‖s - c‖ ≤ r`, `a ≤ Im s ≤ B`, `1/2 ≤ Re s ≤ 1`;
      * `slabClear_of_right_half` -- the reflection `ρ ↦ 1 - conj ρ` (Im-preserving) folds
                               `0 < Re < 1/2` onto `1/2 < Re < 1`, so the right half of a slab suffices.

    conjecture1_proved = False.  A finite, local nonvanishing statement; nothing about RH.
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

theorem ArbEcon.Off.norm_add_nat_le (K : ℕ) (σc tc U : ℝ) (hσc : 0 ≤ σc) (hU0 : 0 ≤ U)
    (hU : (σc + (2 * K - 1 : ℝ)) ^ 2 + tc ^ 2 ≤ U ^ 2) :
    ∀ j, j < 2 * K → ‖sOfG σc tc + j‖ ≤ U := by sorry
