-- Prove2me | Theorems.Thm_Arb4_k6B_sound
-- name    : Arb4.k6B_sound
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:00:55.284316+00:00
-- url     : https://prove2.me/theorems/e05f43bd-5660-4a11-b81a-648df34918ec
-- title:
--   Soundness of the gamma side bounds
-- statement:
--   Let $G_0,G_1$ contain heights $T_0,T_1$, and let $L_4,H_4,L_5,H_5$ be rational
--   bounds. Suppose the finite checker $\operatorname{k6B}$ accepts those data. Then
--   $T_0,T_1\ge0$ and, using the gamma-side functions $S_{-1},S_2$ and their error
--   bounds $e_{-1},e_2$ defined with the certificate,
--   $$\begin{aligned}
--   L_4&\le S_{-1}(T_1)-S_{-1}(T_0)-e_{-1}(T_1),&
--   S_{-1}(T_1)-S_{-1}(T_0)+e_{-1}(T_0)&\le H_4,\\
--   L_5&\le S_2(T_1)-S_2(T_0)-e_2(T_1),&
--   S_2(T_1)-S_2(T_0)+e_2(T_0)&\le H_5.
--   \end{aligned}$$
--   All rational values are interpreted in the reals.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/Arb4_Gamma.lean#L387-L419

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
import Theorems.Thm_Arb4_arctan_mem
import Theorems.Thm_RSDesignTheta_logpi_box
namespace Arb4.Q
end Arb4.Q
namespace RSDesignTheta
end RSDesignTheta
namespace ThetaGap
end ThetaGap
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
























/-! ## D. The closed-form Γℝ brackets at one height -/



section
namespace Arb4.GamD
end Arb4.GamD
open Arb4.GamD













end















/-! ## E. The K6b comparisons of a band -/

theorem Arb4.k6B_sound (G0 G1 : GamD) (L4 H4 L5 H5 : Q) (h : k6B G0 G1 L4 H4 L5 H5 = true) :
    0 ≤ G0.T.val ∧ 0 ≤ G1.T.val ∧
      L4.val ≤ ArgGammaR.Sm1 G1.T.val - ArgGammaR.Sm1 G0.T.val - ArgGammaR.em1 G1.T.val ∧
      ArgGammaR.Sm1 G1.T.val - ArgGammaR.Sm1 G0.T.val + ArgGammaR.em1 G0.T.val ≤ H4.val ∧
      L5.val ≤ ArgGammaR.S2 G1.T.val - ArgGammaR.S2 G0.T.val - ArgGammaR.e2 G1.T.val ∧
      ArgGammaR.S2 G1.T.val - ArgGammaR.S2 G0.T.val + ArgGammaR.e2 G0.T.val ≤ H5.val := by sorry
