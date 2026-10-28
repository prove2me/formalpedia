-- Prove2me | Theorems.Thm_Arb4_edgeOK_sound
-- name    : Arb4.edgeOK_sound
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:35:05.224268+00:00
-- url     : https://prove2.me/theorems/de60c7b1-3a5e-429b-8589-0cb6918cab14
-- title:
--   Soundness of a horizontal-edge certificate
-- statement:
--   Let $E$ be the recorded horizontal-edge data, with height $T$ and rational interval
--   endpoints $L,H$. If its Boolean edge checker succeeds, then the change of argument
--   of the Riemann zeta function along the segment from $2+iT$ to $-1+iT$ satisfies
--   $$\operatorname{edgeOK}(E)=\mathrm{true}\quad\Longrightarrow\quad
--   \Delta_{[2,-1]+iT}\arg\zeta\in[L,H].$$
--   The interval endpoints are the real values of $E$'s stored rational bounds.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/Arb4_Edge.lean#L300-L357

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Edge
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
import Theorems.Thm_Arb4_pieceOK_sound
import Theorems.Thm_ArbEcon_Off_checkG_sound
import Theorems.Thm_ArbEcon_Off_initO_sound
import Theorems.Thm_ArbEcon_Off_stepO_sound
import Theorems.Thm_ArbEcon_OrderK_valid64
import Theorems.Thm_ArctanTaylor_arctan_le_self
import Theorems.Thm_ArctanTaylor_self_sub_cube_le_arctan
import Theorems.Thm_ArgHoriz_hAH_of_octCert_boxes
namespace Arb4.Q
end Arb4.Q
namespace ArbEcon
end ArbEcon
namespace ArbEcon.Off
end ArbEcon.Off
namespace ArbEcon.OrderK
end ArbEcon.OrderK
namespace ZetaReflection
end ZetaReflection
namespace ZetaReflection.EMHigh
end ZetaReflection.EMHigh
/-  Arb4_Edge.lean -- lane Arb4 (h1000 compaction): ONE Boolean kernel checker per horizontal edge.

    `ArgHoriz.hAH_of_octCert_boxes` (brick K6c) reduces `argChangeHoriz ζ T 2 (-1) ∈ [Lo, Hi]` to an
    octant certificate (breakpoints `2 = x 0 > … > x m = -1`, labels, no crossing on every piece),
    two endpoint point enclosures with their corner slopes, and two final inequalities with `π` and
    `arctan`.  The generated edge modules `H1000Edge_*` prove these by `norm_num` per piece and per
    edge.  Here the WHOLE edge is one Boolean `edgeOK`, run by ONE `decide +kernel`:

      * `EdgeD`         -- the certificate data of an edge: height `t = tn / 2^tq`, EM cut `N`, log
                           bound `L`, breakpoints `x`, pieces `pc` (`Arb4_Side.PieceD`), endpoint
                           boxes (`ArbEcon.Off.checkG` data), corner slopes, the final `[Lo, Hi]`;
      * `boxOK`, `boxOK_sound` -- an endpoint enclosure (evaluator run at the piece center, recomputed)
                           and its four corner conditions;
      * `atanLoQ atanHiQ piL piH`, `finalLo_sound`, `finalHi_sound` -- the two final inequalities
                           (`3.141592 < π < 3.141593`, `ArgHoriz.atanLo_le`, `ArgHoriz.le_atanHi`);
      * `edgeOK`, `edgeOK_sound` -- THE EDGE: `edgeOK E = true` gives
                           `argChangeHoriz riemannZeta (tn / 2^tq) 2 (-1) ∈ [Lo, Hi]`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.  One edge of a finite
    zero count; nothing here bears on the Riemann Hypothesis.
-/


open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

section
namespace Arb4
end Arb4
open Arb4

open Q

/-! ## A. Small Boolean helpers -/









/-! ## B. The evaluator invariants of a piece center -/



/-! ## C. Endpoint enclosures and their corner slopes -/









/-! ## D. The two final inequalities -/



























/-! ## E. THE EDGE -/



section
namespace Arb4.EdgeD
end Arb4.EdgeD
open Arb4.EdgeD





end




set_option maxHeartbeats 1000000

theorem Arb4.edgeOK_sound (E : EdgeD) (h : edgeOK E = true) :
    DiffractionCore.argChangeHoriz riemannZeta E.T 2 (-1) ∈ Set.Icc E.Lo.val E.Hi.val := by sorry
