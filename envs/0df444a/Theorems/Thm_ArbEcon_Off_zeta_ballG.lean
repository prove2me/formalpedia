-- Prove2me | Theorems.Thm_ArbEcon_Off_zeta_ballG
-- name    : ArbEcon.Off.zeta_ballG
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:57:02.662063+00:00
-- url     : https://prove2.me/theorems/5ab9817f-0f90-4321-87f5-c6a4cb1df81b
-- title:
--   Off-line zeta enclosure from partial-sum accumulators
-- statement:
--   Let $P,K\in\mathbb N$, $N\ge2$, and $s=\sigma+it$. Suppose accumulators $x_1,x_2$
--   satisfy the defined precision-$P$ enclosure predicates for the zeroth partial
--   sums after $N-1$ and $N$ terms. Suppose
--   $|\zeta(s)-\operatorname{emFinite}(K,s,N)|\le E$, and $B_r,B_i$ are the
--   defined real and imaginary correction components at $s$.
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
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/EMZetaOfflineCheck.lean#L320-L409

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCore
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSound
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_Probes_ArbEconomics_Zeta
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Config64
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
namespace ArbEcon
end ArbEcon
namespace ArbEcon.OrderK
end ArbEcon.OrderK
namespace ZetaReflection
end ZetaReflection
namespace ZetaReflection.EMHigh
end ZetaReflection.EMHigh
/-  EMZetaOfflineCheck.lean -- lane offline: the KERNEL-ONLY assembly of an order-(2K+1)
    Euler-Maclaurin enclosure of ζ(σ + i t) at a rational `σ = (a - b)/q` (any sign, `σ > -2K`) and a
    dyadic `t = tn / 2^tq > 0`.

      * `gpochG`, `pochRI_eq_gpochG`  -- the Gaussian-integer rising factorial
                                         `(q u)^k (σ + i t)_k` (`u = 2^tq`);
      * `corrDataG`, `corr_eqG`       -- the exact correction factor `emCorr K (σ + i t) N` as
                                         `(BreN + i BimN) / BD` in integers;
      * `pnG`, `pochNormSq_eq_pnG`    -- the remainder numerator `Π_{j<k} ((sN + j q)² u² + tn² q²)`;
      * `rpow_neg_le_of_pow`          -- `N^(-σ) ≤ Rn/Rd` from `Rd^q N^b ≤ Rn^q N^a`;
      * `remOddG`, `remOddG_sound`    -- the odd-saw remainder of `EMOff.em_zeta_orderK_enclosure_odd_ext`
                                         (valid off the line, `σ > -2K`) as `EN/ED`;
      * `zeta_ballG`                  -- the evaluator balls after `N-1` and `N` terms plus any remainder
                                         bound give balls for `Re ζ(s)`, `Im ζ(s)`;
      * `checkG`, `checkG_sound`      -- ONE Boolean checker (run by `decide +kernel`) and its
                                         soundness: `lo/D ≤ Re ζ(σ + i t) ≤ hi/D`, same for `Im`.

    conjecture1_proved = False.  Finite interval arithmetic at one point; nothing about RH.
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

open ArbEcon.OrderK (betaN Lbeta  )

/-! ## A. The Gaussian-integer rising factorial at `σ = sN/q`, `t = tn/u`. -/















/-! ## B. The remainder numerator and `N^(-σ)`. -/







/-! ## C. The odd-saw remainder certificate, off the line. -/





/-! ## D. The ball: evaluator invariants + remainder + correction factor. -/

theorem ArbEcon.Off.zeta_ballG (P : ℕ) (σ t : ℝ) (K N : ℕ) (hN : 2 ≤ N) (x1 x2 : Acc)
    (h1 : AccOK P (psumK σ t 0 (N - 1)) x1) (h2 : AccOK P (psumK σ t 0 N) x2) (E : ℝ)
    (hE : ‖riemannZeta (sOfG σ t) - emFinite K (sOfG σ t) N‖ ≤ E) (Bre Bim : ℝ)
    (hBre : emCorrRe K σ t N = Bre) (hBim : emCorrIm K σ t N = Bim) :
    let a1 := (x1.reP : ℝ) - x1.reN
    let b1 := (x1.imP : ℝ) - x1.imN
    let za := ((x2.reP : ℝ) - x2.reN) - a1
    let zb := ((x2.imP : ℝ) - x2.imN) - b1
    let zra := (x2.reR : ℝ) + x1.reR
    let zrb := (x2.imR : ℝ) + x1.imR
    |(riemannZeta (sOfG σ t)).re * 2 ^ P - (a1 + za * Bre - zb * Bim)|
        ≤ x1.reR + zra * |Bre| + zrb * |Bim| + E * 2 ^ P ∧
    |(riemannZeta (sOfG σ t)).im * 2 ^ P - (b1 + za * Bim + zb * Bre)|
        ≤ x1.imR + zra * |Bim| + zrb * |Bre| + E * 2 ^ P := by sorry
