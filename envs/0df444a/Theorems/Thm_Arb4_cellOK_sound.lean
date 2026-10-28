-- Prove2me | Theorems.Thm_Arb4_cellOK_sound
-- name    : Arb4.cellOK_sound
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:24:44.38701+00:00
-- url     : https://prove2.me/theorems/3442ee81-2e32-4758-a39e-6dbad741cef4
-- title:
--   Soundness of a zero-free slab cell
-- statement:
--   Let $S$ be slab data with heights $\ell,h$ and consecutive real cell endpoints
--   $x_j,x_{j+1}$. If its slab-header check and its $j$th cell check both succeed, then
--   $$x\in[\min(x_j,x_{j+1}),\max(x_j,x_{j+1})],\quad
--   \ell\le y\le h,\quad\tfrac12\le x\le1
--   \quad\Longrightarrow\quad\zeta(x+iy)\ne0.$$
--   This is the analytic conclusion of the finite cell certificate.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/Arb4_Slab.lean#L158-L229

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Edge
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Q
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Side
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Slab
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
import Theorems.Thm_Arb4_val_emcBQ
import Theorems.Thm_ArbEcon_Off_CK_le
import Theorems.Thm_ArbEcon_Off_dist_le_of_box
import Theorems.Thm_ArbEcon_Off_initO_sound
import Theorems.Thm_ArbEcon_Off_stepO_sound
import Theorems.Thm_ArbEcon_OrderK_valid64
import Theorems.Thm_H1000Oct_cell_zeta_ne_zero_R
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
/-  Arb4_Slab.lean -- lane Arb4 (h1000 compaction): ONE Boolean kernel checker per zero-free
    edge-clearance slab `EdgeClearGlue.SlabClear a b` (brick K1's numerical input).

    The generated slab modules `H1000Slab_*` of lane h1000-integrate cover `[1/2, 1] × [a, b]` by
    cells (one off-line evaluator run and one `ArbEcon.Off.checkCell` each), assembled by
    `H1000Oct.cell_zeta_ne_zero_R`, and close the slab budget, the Pochhammer bound and about
    fifteen scalar conditions per cell by `norm_num`.  Here the WHOLE slab is one Boolean `slabOK`:

      * `slabBudgetQ`, `slabBudget_le` -- the slab error budget as a rational (with
                           `C_6 ≤ 84107 · 10^-15`, `H1000Oct.CK_six_le`);
      * `CellD`, `SlabD` -- the certificate data: the slab `[lo, hi]`, its shared budget, the
                           breakpoints `1/2 = xs 0 < … < xs m = 1` and one cell per column
                           `[xs j, xs (j+1)] × [lo, hi]` (center, radius, half-widths);
      * `cellOK`, `cellOK_sound` -- one cell (evaluator run recomputed, `checkCell`, geometry);
      * `slabOK`, `slabOK_sound` -- THE SLAB: `slabOK S = true` gives `SlabClear lo hi`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.  A finite zero-free
    slab; nothing here bears on the Riemann Hypothesis.
-/


open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

section
namespace Arb4
end Arb4
open Arb4

open Q

/-! ## A. The slab budget -/





/-! ## B. The certificate data -/





section
namespace Arb4.CellD
end Arb4.CellD
open Arb4.CellD









end

/-! ## C. One cell -/








set_option maxHeartbeats 1000000

theorem Arb4.cellOK_sound (S : SlabD) (hS : slabHeadOK S = true) (j : ℕ) (h : cellOK S j = true) :
    ∀ x y : ℝ, x ∈ Set.uIcc (S.xs j).val (S.xs (j + 1)).val →
      S.lo.val ≤ y → y ≤ S.hi.val → 1 / 2 ≤ x → x ≤ 1 →
      riemannZeta ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by sorry
