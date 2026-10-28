-- Prove2me | Theorems.Thm_Arb4_arctan_mem
-- name    : Arb4.arctan_mem
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:57:13.664063+00:00
-- url     : https://prove2.me/theorems/ed23aa48-7574-4da1-b797-7d70a0420b98
-- title:
--   Soundness of an arctangent enclosure
-- statement:
--   Let $y$ be a stored rational, and let $N$ and $m$ be natural-number parameters.
--   If the arctangent check for $y,m$ succeeds, the defined lower and upper rational
--   approximations enclose the real arctangent:
--   $$\operatorname{atanOK}(y,m)=\mathrm{true}\quad\Longrightarrow\quad
--   \operatorname{atanLo}(y,N,m)\le\arctan(y)\le\operatorname{atanHi}(y,N,m).$$
--   Each stored rational in the displayed inequality is interpreted by its real value.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/Arb4_Gamma.lean#L213-L256

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_RSTheta
import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Edge
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Gamma
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Q
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Side
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Definitions.Def_ArdaRH65K_Turing121_ArgGammaR
import Definitions.Def_ArdaRH65K_Turing121_ArgHoriz
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
import Definitions.Def_ArdaRH65K_Turing121_H1000Octant
import Definitions.Def_ArdaRH65K_Turing121_Probes_ArbEconomics_Zeta
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Definitions.Def_ArdaRH65K_Turing121_TuringBand
import Definitions.Def_ArdaRH65K_XiLineZeros
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Config64
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_Arb4_Q_val_div
import Theorems.Thm_ArctanTaylor_arctan_eq_ps_add_rem
import Theorems.Thm_ArctanTaylor_rem_abs_le
namespace Arb4.Q
end Arb4.Q
namespace ZetaReflection
end ZetaReflection
namespace ZetaReflection.EMHigh
end ZetaReflection.EMHigh
/-  Arb4_Gamma.lean -- lane Arb4 (h1000 compaction): the Γℝ argument-change side conditions of a
    Turing band (brick K6b, `ArgGammaR`) as ONE Boolean kernel check.

    `ArgChangeGlue.K6Side` compares the band's enclosures `[L4, H4]`, `[L5, H5]` with the closed-form
    brackets `Sm1`, `S2` of `ArgGammaR` at the two edge heights.  The generated module
    `ArgChangeH1000` proves one `log` box, one `arctan` box and one `S2`/`Sm1` box per height by
    `norm_num` over truncated series (about 1 MB of olean per height).  Here:

      * `logOK logLo logHi`, `log_mem`  -- `log v = k log 2 + log (1 - x)`, `v = 2^k (1 - x)`,
                             `0 ≤ x < 1`, with `RSDesignTheta.log2_box` and the Taylor bracket
                             `ArgGammaR.log_one_sub_mem` (n terms);
      * `atanOK arctanLo arctanHi`, `arctan_mem` -- `arctan y` by the Taylor bracket
                             `ArctanTaylor.arctan_bracket` (mode 0, `0 ≤ y ≤ 1`), by
                             `arctan y = π/2 - arctan (1/y)` (mode 1, `y > 0`), or `π/4` (`y = 1`);
      * `GamD`, `gamOK`, `S2_mem`, `Sm1_mem` -- the brackets at one height (`ArgGammaR.S2_mem_of`,
                             `Sm1_mem_of`, `RSDesignTheta.logpi_box`, `π` to 20 digits);
      * `k6B`, `k6B_sound` -- the four K6b comparisons of a band from two heights.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.
-/



open scoped Real

section
namespace Arb4
end Arb4
open Arb4

open Q

/-! ## A. Constants -/
















/-! ## B. Logarithms -/






























/-! ## C. Arctangents -/

theorem Arb4.arctan_mem (y : Q) (N mode : ℕ) (h : atanOK y mode = true) :
    (arctanLo y N mode).val ≤ Real.arctan y.val ∧ Real.arctan y.val ≤ (arctanHi y N mode).val := by sorry
