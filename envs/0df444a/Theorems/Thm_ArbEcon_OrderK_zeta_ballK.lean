-- Prove2me | Theorems.Thm_ArbEcon_OrderK_zeta_ballK
-- name    : ArbEcon.OrderK.zeta_ballK
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:57:06.246459+00:00
-- url     : https://prove2.me/theorems/581b5651-3eb5-44c6-b682-24d0f6ac9be7
-- title:
--   Critical-line zeta enclosure from partial-sum states
-- statement:
--   Let $c$ be an evaluator configuration of precision $P$, $N\ge2$, $K\in\mathbb N$,
--   and $s=1/2+it$. Suppose states $x_1,x_2$ satisfy the defined evaluator invariants
--   after $N-1$ and $N$ terms. Suppose $|\zeta(s)-\operatorname{emFinite}(K,s,N)|\le E$,
--   and $B_r,B_i$ are the defined real and imaginary correction components at $s$.
--
--   For $i=1,2$ write $a_i=x_i.\mathrm{reP}-x_i.\mathrm{reN}$,
--   $b_i=x_i.\mathrm{imP}-x_i.\mathrm{imN}$, $z_a=a_2-a_1$, $z_b=b_2-b_1$,
--   $R_a=x_1.\mathrm{reR}+x_2.\mathrm{reR}$, and
--   $R_b=x_1.\mathrm{imR}+x_2.\mathrm{imR}$, after casting to reals. Then
--   $$|2^P\operatorname{Re}\zeta(s)-(a_1+z_aB_r-z_bB_i)|
--   \le x_1.\mathrm{reR}+R_a|B_r|+R_b|B_i|+2^PE,$$
--   $$|2^P\operatorname{Im}\zeta(s)-(b_1+z_aB_i+z_bB_r)|
--   \le x_1.\mathrm{imR}+R_a|B_i|+R_b|B_r|+2^PE.$$
--   These are the real and imaginary zeta enclosures.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/EMZetaHighEval.lean#L41-L131

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_Probes_ArbEconomics_Zeta
import Definitions.Def_ArdaRS_Arithmetic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Exponential
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
import Theorems.Thm_ZetaReflection_EMHigh_emCorr_re_im
namespace ZetaReflection
end ZetaReflection
namespace ZetaReflection.EMHigh
end ZetaReflection.EMHigh
/-  EMZetaHighEval.lean -- the order-(2K+1) Euler-Maclaurin enclosure of ζ on the critical line,
    wired to the Nat-only kernel evaluator of the ArbEconomics seat (lane emhigh).

    Chain (all proved here, no numeric hypotheses):
      * `emFinite_line_split` : `emFinite K (1/2+it) N = psum t (N-1) + N^(-s) · emCorr K s N`;
      * `emCorr_line_re_im`   : `Re/Im emCorr K s N = emCorrRe/emCorrIm K (1/2) t N`
                                (closed real forms, `EMZetaHigh.emCorr_re_im`);
      * `zeta_ballK`          : two evaluator invariants (after `N-1` and `N` terms, from
                                `ArbEcon.chunk_sound`) plus ANY remainder bound `E` of the
                                order-(2K+1) finite part give explicit balls for Re ζ and Im ζ;
      * `zetaK_re_bounds` / `zetaK_im_bounds` : final forms `lo ≤ Re/Im ζ(1/2+it) ≤ hi` from rational
                                side conditions (checked per instance by `norm_num`).
    The remainder `E` comes from `EMZetaHigh.em_line_remainder_le` (general K, proved).

    conjecture1_proved = False.  Finite interval arithmetic at one height; nothing about RH.
-/



open Complex ZetaReflection ZetaReflection.EMHigh

section
namespace ArbEcon
end ArbEcon
open ArbEcon

section
namespace ArbEcon.OrderK
end ArbEcon.OrderK
open ArbEcon.OrderK

theorem ArbEcon.OrderK.zeta_ballK (c : Cfg) (K : ℕ) (t : ℝ) (N : ℕ) (hN : 2 ≤ N) (s1 s2 : St)
    (h1 : Inv c t (N - 1) s1) (h2 : Inv c t N s2) (E : ℝ)
    (hE : ‖riemannZeta (sOf t) - emFinite K (sOf t) N‖ ≤ E) (Bre Bim : ℝ)
    (hBre : emCorrRe K (1 / 2) t N = Bre) (hBim : emCorrIm K (1 / 2) t N = Bim) :
    let a1 := (s1.reP : ℝ) - s1.reN
    let b1 := (s1.imP : ℝ) - s1.imN
    let za := ((s2.reP : ℝ) - s2.reN) - a1
    let zb := ((s2.imP : ℝ) - s2.imN) - b1
    let zra := (s2.reR : ℝ) + s1.reR
    let zrb := (s2.imR : ℝ) + s1.imR
    |(riemannZeta (sOf t)).re * 2 ^ c.P - (a1 + za * Bre - zb * Bim)|
        ≤ s1.reR + zra * |Bre| + zrb * |Bim| + E * 2 ^ c.P ∧
    |(riemannZeta (sOf t)).im * 2 ^ c.P - (b1 + za * Bim + zb * Bre)|
        ≤ s1.imR + zra * |Bim| + zrb * |Bre| + E * 2 ^ c.P := by sorry
