-- Prove2me | Theorems.Thm_ArbEcon_Off_checkCell_sound
-- name    : ArbEcon.Off.checkCell_sound
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:00:55.337845+00:00
-- url     : https://prove2.me/theorems/1047eb15-e678-4645-9489-2bac17bb4344
-- title:
--   Soundness of a zero-free cell inequality
-- statement:
--   Let $c,o$ be configurations, $\sigma=(o.a-o.b)/o.q$, $t=c.t_n/2^{c.t_q}$,
--   $K,N,p,r_n,r_d,F_n,F_d\in\mathbb N$, and $s=\sigma+it$. Let accumulator lists
--   $x_1,x_2$ satisfy the defined list enclosure predicates for the partial-sum
--   weights after $N-1$ and $N$ terms. If the defined $\operatorname{checkCell}$
--   returns true, then, with $r=r_n/r_d$ and $F=F_n/F_d$,
--   $$\sum_{k=1}^p\frac{|W_k(K,N,s)|r^k}{k!}+F<|W_0(K,N,s)|.$$
--   The quotients use Lean's total real division. This validates the arithmetic
--   inequality needed for zero exclusion.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/EMZetaOfflineSlabCheck.lean#L226-L358

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCore
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlab
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSound
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_Probes_ArbEconomics_Zeta
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Config64
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
import Theorems.Thm_ArbEcon_Off_corr_eqG
import Theorems.Thm_ArbEcon_Off_wball_sound
import Theorems.Thm_ZetaReflection_EMHigh_emCorr_re_im
namespace ZetaReflection
end ZetaReflection
namespace ZetaReflection.EMHigh
end ZetaReflection.EMHigh
/-  EMZetaOfflineSlabCheck.lean -- lane offline: the KERNEL checker of a zero-free cell.

    The off-line evaluator run at a center `c = σc + i tc` with `p + 1` accumulators gives, after
    `N - 1` and `N` terms, balls of `S_k = Σ_{n<N} (log n)^k n^(-c)` and of `S_k + (log N)^k N^(-c)`.
    With the exact correction factor `emCorr K c N = (BreN + i BimN)/BD` (`corrDataG`) they give balls
    of the Taylor weights `W_k = S_k + (log N)^k N^(-c) emCorr K c N` of `EMZetaOfflineSlab`.

      * `wData`, `wball_sound`  -- the ball of `W_k`, scaled by `2^P BD`;
      * `sumM`, `sumM_sound`    -- `Σ_{k≥1} ‖W_k‖ rn^k rd^(p-k) (p!/k!)` from above;
      * `checkCell`, `checkCell_sound` -- ONE Boolean check (run by `decide +kernel`) proving
                                   `Σ_{k=1}^p ‖W_k‖ r^k/k! + FN/FD < ‖W_0‖`, `r = rn/rd`, the
                                   hypothesis `hmain` of `zeta_ne_zero_of_cell`.

    conjecture1_proved = False.  Finite interval arithmetic; nothing about RH.
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

/-! ## A. The Taylor weights from the evaluator's partial sums. -/



/-! ## B. The ball of a weight. -/









/-! ## C. The weighted sum over `k ≥ 1`. -/





/-! ## D. The cell checker. -/








set_option maxHeartbeats 2000000

theorem ArbEcon.Off.checkCell_sound (c : Cfg) (o : OCfg) (σ t : ℝ) (hσ : σ = ((o.a : ℝ) - o.b) / o.q)
    (ht : t = (c.tn : ℝ) / 2 ^ c.tq) (K N p : ℕ) (xs1 xs2 : List Acc) (rn rd FN FD : ℕ)
    (h1 : AccsOK c.P (fun k => psumK σ t k (N - 1)) 0 xs1)
    (h2 : AccsOK c.P (fun k => psumK σ t k N) 0 xs2)
    (hc : checkCell c o K N p xs1 xs2 rn rd FN FD = true) :
    ∑ k ∈ Finset.Ico 1 (p + 1), ‖Wk K N (sOfG σ t) k‖ * ((rn : ℝ) / rd) ^ k / (k ! : ℝ)
      + (FN : ℝ) / FD < ‖Wk K N (sOfG σ t) 0‖ := by sorry
