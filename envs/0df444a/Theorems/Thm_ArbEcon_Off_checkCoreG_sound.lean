-- Prove2me | Theorems.Thm_ArbEcon_Off_checkCoreG_sound
-- name    : ArbEcon.Off.checkCoreG_sound
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:58:21.016514+00:00
-- url     : https://prove2.me/theorems/8e9ce3f9-fc49-4561-a6fe-f330043aed99
-- title:
--   Soundness of the off-line enclosure core
-- statement:
--   Let $P,t_q,t_n,K,a,b,q,N,D\in\mathbb N$, $\sigma=(a-b)/q$,
--   $t=t_n/2^{t_q}$, and $s=\sigma+it$. Let accumulators $x_1,x_2$ satisfy the
--   defined precision-$P$ predicates for the zeroth partial sums after $N-1$ and $N$
--   terms. Suppose $|\zeta(s)-\operatorname{emFinite}(K,s,N)|\le E_n/E_d$ and the
--   defined $\operatorname{checkCoreG}$ returns true for integer bounds
--   $r_l,r_h,i_l,i_h,E_n,E_d$. Then
--   $$r_l/D\le\operatorname{Re}\zeta(s)\le r_h/D,\qquad
--   i_l/D\le\operatorname{Im}\zeta(s)\le i_h/D.$$
--   All quotients use Lean's total real division.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/EMZetaOfflineCheck.lean#L449-L539

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
import Theorems.Thm_ArbEcon_Off_corr_eqG
import Theorems.Thm_ArbEcon_Off_zeta_ballG
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







/-! ## E. The kernel checker and its soundness. -/






set_option maxHeartbeats 1000000

theorem ArbEcon.Off.checkCoreG_sound (P tq tn K : ℕ) (a b q N : ℕ) (σ t : ℝ) (hσ : σ = ((a : ℝ) - b) / q)
    (ht : t = (tn : ℝ) / 2 ^ tq) (x1 x2 : Acc)
    (h1 : AccOK P (psumK σ t 0 (N - 1)) x1) (h2 : AccOK P (psumK σ t 0 N) x2) (D : ℕ)
    (reLo reHi imLo imHi EN ED : ℤ)
    (hE : ‖riemannZeta (sOfG σ t) - emFinite K (sOfG σ t) N‖ ≤ (EN : ℝ) / (ED : ℝ))
    (hc : checkCoreG P tq tn K ((a : ℤ) - b) q N x1 x2 D reLo reHi imLo imHi EN ED = true) :
    ((reLo : ℝ) / D ≤ (riemannZeta (sOfG σ t)).re ∧ (riemannZeta (sOfG σ t)).re ≤ (reHi : ℝ) / D) ∧
    ((imLo : ℝ) / D ≤ (riemannZeta (sOfG σ t)).im ∧ (riemannZeta (sOfG σ t)).im ≤ (imHi : ℝ) / D) := by sorry
