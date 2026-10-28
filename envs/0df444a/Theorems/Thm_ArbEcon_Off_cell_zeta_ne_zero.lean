-- Prove2me | Theorems.Thm_ArbEcon_Off_cell_zeta_ne_zero
-- name    : ArbEcon.Off.cell_zeta_ne_zero
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:17:21.613531+00:00
-- url     : https://prove2.me/theorems/700793f2-7fd0-47b6-bd3b-d5a8ff82768b
-- title:
--   Certified zero-free cell in the right half of the strip
-- statement:
--   Let $c,o$ be configurations with center $s_c=\sigma_c+it_c$ given by
--   $\sigma_c=(o.a-o.b)/o.q$, $t_c=c.t_n/2^{c.t_q}$. Let $K\ge1$, $N\ge2$, and
--   let states $x_1,x_2$ satisfy the defined off-line invariants after $N-1$ and
--   $N$ terms. Suppose $\operatorname{checkCell}$ succeeds for radius $r=r_n/r_d$,
--   budget $F=F_n/F_d$, and order $p$. Let $L,a,U,B,Q\in\mathbb R$ and
--   $r_0\in\mathbb N$ satisfy
--   $$x_2.\mathrm{lhi}\le2^{c.P}L,\quad rL\le1,\quad 0<a\le t_c,\quad
--   \sigma_c\ge0,\quad U\ge0,\quad (\sigma_c+2K-1)^2+t_c^2\le U^2,$$
--   $$Q\ge0,\quad \operatorname{pochNormSq}(1,B,2K+1)\le Q^2,\quad
--   r_0>0,\quad r_0^2\le N,$$
--   and, using the defined $C_p$, $\operatorname{emcB}$, $\operatorname{corrVar}$,
--   and $C_K$,
--   $$C_p(rL)^{p+1}(N-1+\operatorname{emcB}(K,N,a,U))
--   +3\operatorname{corrVar}(K,N,r,a,U)
--   +\frac{C_KQ}{N^{2K}r_0(2K+1/2)}\le F.$$
--   Then $\zeta(s)\ne0$ whenever $|s-s_c|\le r$, $a\le\operatorname{Im}s\le B$,
--   and $1/2\le\operatorname{Re}s\le1$. Real division is totalized as in Lean.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/EMZetaOfflineSlabClear.lean#L51-L97

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
import Theorems.Thm_ArbEcon_Off_checkCell_sound
import Theorems.Thm_ArbEcon_Off_em_remainder_region
import Theorems.Thm_ArbEcon_Off_norm_add_nat_le
import Theorems.Thm_ArbEcon_Off_norm_emCorr_le
import Theorems.Thm_ArbEcon_Off_zeta_ne_zero_of_cell
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

theorem ArbEcon.Off.cell_zeta_ne_zero (c : Cfg) (o : OCfg) (σc tc : ℝ) (hσ : σc = ((o.a : ℝ) - o.b) / o.q)
    (ht : tc = (c.tn : ℝ) / 2 ^ c.tq) (K N p : ℕ) (hK : 1 ≤ K) (hN : 2 ≤ N) (s1 s2 : StO)
    (h1 : InvO c σc tc (N - 1) s1) (h2 : InvO c σc tc N s2) (rn rd FN FD : ℕ)
    (hchk : checkCell c o K N p s1.acc s2.acc rn rd FN FD = true)
    (L a U B Qr : ℝ) (r0 : ℕ) (hL : (s2.lhi : ℝ) ≤ L * 2 ^ c.P) (hrL : (rn : ℝ) / rd * L ≤ 1)
    (ha : 0 < a) (hta : a ≤ tc) (hσc : 0 ≤ σc) (hU0 : 0 ≤ U)
    (hU : (σc + (2 * K - 1 : ℝ)) ^ 2 + tc ^ 2 ≤ U ^ 2) (hQr0 : 0 ≤ Qr)
    (hQ : pochNormSq 1 B (2 * K + 1) ≤ Qr ^ 2) (hr0 : 0 < r0) (hr0N : r0 ^ 2 ≤ N)
    (hbudget : Cp p * ((rn : ℝ) / rd * L) ^ (p + 1) * (((N : ℝ) - 1) + emcB K N a U)
        + 3 * corrVar K N ((rn : ℝ) / rd) a U
        + CK K * Qr / ((N : ℝ) ^ (2 * K) * r0) / (((2 * K : ℕ) : ℝ) + 1 / 2) ≤ (FN : ℝ) / FD) :
    ∀ s : ℂ, ‖s - sOfG σc tc‖ ≤ (rn : ℝ) / rd → a ≤ s.im → s.im ≤ B → 1 / 2 ≤ s.re → s.re ≤ 1 →
      riemannZeta s ≠ 0 := by sorry
