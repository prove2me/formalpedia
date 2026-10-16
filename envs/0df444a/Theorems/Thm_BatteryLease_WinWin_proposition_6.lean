-- Prove2me | Theorems.Thm_BatteryLease_WinWin_proposition_6
-- name    : BatteryLease.WinWin.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:20:18.546851+00:00
-- url     : https://prove2.me/theorems/cf0f3f46-7828-41ce-a2ce-d86b62c0db47
-- title:
--   Proposition 6, p. 18 — win-win-win: for c_h near a(1−ρ)/2 and then r_h near a, flexible leasing raises profit and lowers total customer cost and total battery capacity
-- statement:
--   Let $a>1$ and $a/(2+a)<\rho<1$, and write $c_0=a(1-\rho)/2$. Compare simple battery leasing (profit $\Pi^b$, total customer cost $CT^b$, total battery capacity $BT^b$, at a profit-maximizing lease rate) with flexible battery leasing (profit $\Pi^f$, $CT^f$, $BT^f$, at a subgame-perfect equilibrium with additional acquisition $Q^f_h$).
--
--   1. **($Q^f_h>0$.)** If $\rho<7a/(8+7a)$, there is $\delta>0$ such that for every $c_h\in(c_0-\delta,c_0)$ there is $R<a$ such that for every $r_h\in(R,a]$: a benchmark optimum and a flexible equilibrium exist, and every benchmark optimum and every flexible equilibrium satisfy
--   $$Q^f_h>0,\qquad \Pi^b<\Pi^f,\qquad CT^f<CT^b,\qquad BT^f<BT^b.$$
--   2. **($Q^f_h=0$.)** There is $\delta>0$ such that for every $c_h\in(c_0,c_0+\delta)$ there is $R<a$ such that for every $r_h\in(R,a]$: a benchmark optimum and a flexible equilibrium exist, and every benchmark optimum and every flexible equilibrium satisfy
--   $$Q^f_h=0,\qquad \Pi^b<\Pi^f,\qquad CT^f<CT^b,\qquad BT^f<BT^b.$$
--
--   Introducing flexible leasing thus benefits the manufacturer, the customers and the environment at once ("win-win-win") when the battery cost is moderate and the high-capacity range is large.
--
--   **Formalization Note** "$c_h$ sufficiently close to $a(1-\rho)/2$, $r_h$ sufficiently large" is read with the quantifier order: first $c_h$ close to $c_0$ (on the branch's side, $c_h\ne c_0$), then $r_h$ close enough to $a$ depending on $c_h$. A single neighbourhood of $(a,c_0)$ in both variables does not work: on the $Q^f_h>0$ side Proposition 5's threshold $T(r_h)$ equals $c_0$ at $r_h=a$ and is below it for $r_h<a$, so $c_h\in(T(r_h),c_0)$ raises capacity, and the other side fails similarly; at $c_h=c_0$, $r_h=a$ the capacities are equal. Each branch asserts that a benchmark optimum and a flexible equilibrium exist, so the comparison is not vacuous. The standing assumptions on $r_h$ and $c_h$ hold automatically near $(a,c_0)$ and are not hypotheses.
-- source:
--   Shi, Hu, Battery as a Service: Flexible Electric Vehicle Battery Leasing, M&SOM (2024), doi:10.1287/msom.2022.0587, authors' manuscript of 13 January 2024, p. 18, Proposition 6; proof Online Appendix p. 8 (PDF 40)

import Mathlib
import Definitions.Def_BatteryLease_WinWin_Setting

namespace BatteryLease.WinWin
theorem proposition_6 (a ρ : ℝ) (ha : 1 < a) (hρ0 : a / (2 + a) < ρ) (hρ1 : ρ < 1) :
    (ρ < 7 * a / (8 + 7 * a) →
      ∃ δ > 0, ∀ ch : ℝ, a * (1 - ρ) / 2 - δ < ch → ch < a * (1 - ρ) / 2 →
        ∃ R < a, ∀ rh : ℝ, R < rh → rh ≤ a →
          (∃ pb, IsBenchOpt a ρ rh ch pb) ∧
          (∃ ph τ pbh pbl, IsFlexEq a ρ rh ch ph τ pbh pbl) ∧
          ∀ pb, IsBenchOpt a ρ rh ch pb → ∀ ph τ pbh pbl, IsFlexEq a ρ rh ch ph τ pbh pbl →
            0 < acq a rh τ ph pbh pbl ∧
            benchProfit a ρ rh ch pb < flexProfit a ρ rh ch ph τ pbh pbl ∧
            flexCC a ρ rh ph pbh pbl < benchCC a ρ rh pb ∧
            flexCap a rh τ ph pbh pbl < benchCap a ρ rh pb) ∧
    (∃ δ > 0, ∀ ch : ℝ, a * (1 - ρ) / 2 < ch → ch < a * (1 - ρ) / 2 + δ →
        ∃ R < a, ∀ rh : ℝ, R < rh → rh ≤ a →
          (∃ pb, IsBenchOpt a ρ rh ch pb) ∧
          (∃ ph τ pbh pbl, IsFlexEq a ρ rh ch ph τ pbh pbl) ∧
          ∀ pb, IsBenchOpt a ρ rh ch pb → ∀ ph τ pbh pbl, IsFlexEq a ρ rh ch ph τ pbh pbl →
            acq a rh τ ph pbh pbl = 0 ∧
            benchProfit a ρ rh ch pb < flexProfit a ρ rh ch ph τ pbh pbl ∧
            flexCC a ρ rh ph pbh pbl < benchCC a ρ rh pb ∧
            flexCap a rh τ ph pbh pbl < benchCap a ρ rh pb) := by sorry
end BatteryLease.WinWin
