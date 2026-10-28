-- Prove2me | Theorems.Thm_Arb4_bandC_of
-- name    : Arb4.bandC_of
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:32:47.325792+00:00
-- url     : https://prove2.me/theorems/cb6ed8dd-943a-4bcc-a7af-a8d42e6e79c3
-- title:
--   Combining point checks with a band check
-- statement:
--   Let $D$ be a finite list of compact points and let $T_0,T_1,n$ be represented by
--   the natural-number parameters of the certificate. If all point checks succeed
--   and the band checker succeeds on the point projections of $D$, then
--   $$\operatorname{bandC}(T_0,T_1,n,D)=\mathrm{true}.$$
--   The two height arguments retain their numerator and denominator parameters in the
--   formal statement.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/Arb4_Line.lean#L158-L160

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

theorem Arb4.bandC_of {T0n T0d T1n T1d n : ℕ} {ds : List PtD} (h1 : ds.all (fun d => ptCheckC d.pt) = true)
    (h2 : H1000Line.bandOk T0n T0d T1n T1d n (ds.map PtD.pt) = true) : bandC T0n T0d T1n T1d n ds = true := by sorry
