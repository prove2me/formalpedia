-- Prove2me | Theorems.Thm_Arb4_bandC_sound
-- name    : Arb4.bandC_sound
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:23:03.725859+00:00
-- url     : https://prove2.me/theorems/b43028f2-6372-460a-8973-52b7518ccc86
-- title:
--   A checked band gives critical-line zeros
-- statement:
--   Let $T_0,T_1$ be the real values of the recorded rational heights, and let $n$ be
--   a natural number. If the compact band checker succeeds on a list $D$, there is a
--   strictly increasing list $t_1,\ldots,t_n$ such that
--   $$T_0\le t_j\le T_1,\qquad \Lambda(1/2+it_j)=0\quad(1\le j\le n),$$
--   where $\Lambda$ is the completed Riemann zeta function. The list may be empty
--   when $n=0$.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/Arb4_Line.lean#L163-L217

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_RSTheta
import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Line
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_H1000Line
import Definitions.Def_ArdaRH65K_Turing121_H1000Phase
import Definitions.Def_ArdaRH65K_Turing121_H1000Point
import Definitions.Def_ArdaRH65K_Turing121_KernelGammaEnvelope
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
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
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
import Theorems.Thm_Arb4_ptCheckC_sound
import Theorems.Thm_H1000Line_chainOk_get
import Theorems.Thm_H1000Line_lastLe_sound
import Theorems.Thm_ZetaReflection_alternating_signs_chain
namespace ArbEcon
end ArbEcon
namespace ArbEcon.OrderK
end ArbEcon.OrderK
/-  Arb4_Line.lean -- lane Arb4 (h1000 compaction): the on-line sign certificate of a Turing band
    with the evaluator states recomputed in the kernel (brick K4 in EM form, `H1000Line`).

    The band modules `H1000Line_Bxx` of lane h1000-prep store, per grid point, the two evaluator
    states after `N - 1` and `N` Dirichlet terms as computable definitions (compiled to IR: about
    20 KB of olean per point).  Here a point is `mkPt tn tq N Q r k nl m pos`, whose states ARE the
    evaluator runs (`ArbEcon.run`), so `H1000Line.ptCheck (mkPt …)` recomputes them, and a whole band
    is ONE Boolean `bandB` run by ONE `decide +kernel`:

      * `mkPt`            -- a point record with recomputed states;
      * `allB`, `allB_sound` -- every point of a list passes `H1000Line.ptCheck`;
      * `bandB`, `bandB_sound` -- the band: `allB` and `H1000Line.bandOk` give the band's verbatim
                             `hLine` (`n` increasing zeros of `completedRiemannZeta` on the critical
                             line in `[T0, T1]`) through `H1000Line.band_sound`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.  Finite interval
    arithmetic and the intermediate value theorem; nothing here bears on the Riemann Hypothesis.
-/


section
namespace Arb4
end Arb4
open Arb4











/-! ## Points with the states computed ONCE (no `dirOk` comparison) -/




















open H1000Line

theorem Arb4.bandC_sound (T0 T1 : ℝ) (T0n T0d T1n T1d n : ℕ) (hT0 : T0 = (T0n : ℝ) / T0d)
    (hT1 : T1 = (T1n : ℝ) / T1d) (ds : List PtD) (h : bandC T0n T0d T1n T1d n ds = true) :
    ∃ xs : List ℝ, xs.length = n ∧ xs.IsChain (· < ·) ∧ (∀ t ∈ xs, T0 ≤ t ∧ t ≤ T1) ∧
      (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0) := by sorry
