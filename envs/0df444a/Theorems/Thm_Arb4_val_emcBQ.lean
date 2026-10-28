-- Prove2me | Theorems.Thm_Arb4_val_emcBQ
-- name    : Arb4.val_emcBQ
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:46:07.951905+00:00
-- url     : https://prove2.me/theorems/6063a75a-61f2-4bba-8f91-b24ab20cb58c
-- title:
--   Real value of an Euler–Maclaurin correction bound
-- statement:
--   Let $K\le6$ and $N>0$ be natural numbers. Let $a,U$ be stored rationals, and
--   suppose the numerator of $a$ is positive. Then
--   $$\operatorname{val}(\operatorname{emcBQ}(K,N,a,U))
--   =\operatorname{emcB}(K,N,\operatorname{val}(a),\operatorname{val}(U)).$$
--   The two functions are the rational and real versions of the same correction bound.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/Arb4_Side.lean#L59-L71

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Q
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Side
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
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
namespace Arb4.Q
end Arb4.Q
namespace ArbEcon
end ArbEcon
namespace ArbEcon.Off
end ArbEcon.Off
namespace ZetaReflection
end ZetaReflection
namespace ZetaReflection.EMHigh
end ZetaReflection.EMHigh
/-  Arb4_Side.lean -- lane Arb4 (h1000 compaction): Boolean kernel checkers, with soundness proved
    once, for the per-piece side conditions of an octant certificate (brick K6c, `H1000Octant`).

    The generated edge modules `H1000Edge_*` of lane h1000-integrate close, per octant piece, an error
    budget, a horizontal remainder bound, a `G` certificate and six scalar conditions by `norm_num`
    (about 400 KB of olean per piece).  Here all of them are ONE Boolean `pieceOK`, run by
    `decide +kernel` on exact rationals (`Arb4_Q`), together with the off-line evaluator run itself
    (the states after `N - 1` and `N` terms are recomputed in the kernel, not stored):

      * `CpQ betaQ emcBQ corrVarQ budgetQ` (+ `val_*`) -- the error budget of
                           `H1000Oct.piece_octX_pos` as a rational, EQUAL to the real one;
      * `pochQ`, `val_pochQ` -- `pochNormSq` as a rational;
      * `PieceD`         -- the certificate data of one piece (center `(a - b)/q`, radius `rn/rd`,
                           octant `kk`, budget `FN/FD`, and the rationals of the side conditions);
      * `gOK remOK geomOK budgetOK` and their soundness -- the `G` bound, the order-13 remainder on the
                           piece, the scalar geometry, the budget;
      * `pieceOK`, `pieceOK_sound` -- THE PIECE: `pieceOK tn tq N L P = true` gives
                           `0 < octX kk (ζ(x + i t))` for every `x` with `|x - σ| ≤ r`, `t = tn / 2^tq`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.  Finite interval
    arithmetic along finitely many segments; nothing here bears on the Riemann Hypothesis.
-/



open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

section
namespace Arb4
end Arb4
open Arb4

open Q

/-! ## A. The error budget as a rational -/

theorem Arb4.val_emcBQ (K N : ℕ) (hK : K ≤ 6) (hN : 0 < N) (a U : Q) (ha : 0 < a.n) :
    (emcBQ K N a U).val = ArbEcon.Off.emcB K N a.val U.val := by sorry
