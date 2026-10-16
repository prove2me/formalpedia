-- Prove2me | Theorems.Thm_BatteryLease_WinWin_proposition_4
-- name    : BatteryLease.WinWin.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:20:13.21502+00:00
-- url     : https://prove2.me/theorems/4e4120e2-d46d-4e95-b2c8-bc9ce66e780f
-- title:
--   Proposition 4, p. 16 — total customer cost is lower under flexible leasing for r_h near a and c_h near a(1−ρ)/2, on both sides
-- statement:
--   Let $a>1$ and $a/(2+a)<\rho<1$, and write $c_0=a(1-\rho)/2$. Then:
--   1. ($Q^f_h>0$ side) there is $\delta>0$ such that for all $r_h\in(a-\delta,a]$ and $c_h\in(c_0-\delta,c_0)$, every benchmark optimum $p^b_h$ and every flexible-leasing equilibrium satisfy $CT^f<CT^b$;
--   2. ($Q^f_h=0$ side) there is $\delta>0$ such that for all $r_h\in(a-\delta,a]$ and $c_h\in[c_0,c_0+\delta)$, every benchmark optimum and every flexible-leasing equilibrium satisfy $CT^f<CT^b$.
--
--   Here $CT^b$ and $CT^f$ are the total customer costs under simple and flexible leasing. Total customer cost is the second of the three quantities in the win-win-win of Proposition 6.
--
--   **Formalization Note** The page's sufficient condition "$r_h$ and $c_h$ are sufficiently large" (first bullet) and "$r_h$ is sufficiently large and $c_h$ is sufficiently small" (second bullet) are read as neighbourhoods of the corner $(r_h,c_h)=(a,c_0)$, where the proof's comparison polynomials have strictly negative limits (Online Appendix pp. 6–7); $c_h<c_0$ resp. $c_h\ge c_0$ is the regime split $Q^f_h>0$ / $Q^f_h=0$ of Proposition 2. The bullets' further clauses ("$a$ sufficiently small …", "$\rho$ sufficiently large", "$a$ and $c_h$ sufficiently small") are not stated.
-- source:
--   Shi, Hu, Battery as a Service: Flexible Electric Vehicle Battery Leasing, M&SOM (2024), doi:10.1287/msom.2022.0587, authors' manuscript of 13 January 2024, p. 16, Proposition 4 (first clause of each bullet); proof Online Appendix pp. 6–7 (PDF 38–39)

import Mathlib
import Definitions.Def_BatteryLease_WinWin_Setting

namespace BatteryLease.WinWin
theorem proposition_4 (a ρ : ℝ) (ha : 1 < a) (hρ0 : a / (2 + a) < ρ) (hρ1 : ρ < 1) :
    (∃ δ > 0, ∀ rh ch : ℝ, a - δ < rh → rh ≤ a →
      a * (1 - ρ) / 2 - δ < ch → ch < a * (1 - ρ) / 2 →
      ∀ pb, IsBenchOpt a ρ rh ch pb → ∀ ph τ pbh pbl, IsFlexEq a ρ rh ch ph τ pbh pbl →
        flexCC a ρ rh ph pbh pbl < benchCC a ρ rh pb) ∧
    (∃ δ > 0, ∀ rh ch : ℝ, a - δ < rh → rh ≤ a →
      a * (1 - ρ) / 2 ≤ ch → ch < a * (1 - ρ) / 2 + δ →
      ∀ pb, IsBenchOpt a ρ rh ch pb → ∀ ph τ pbh pbl, IsFlexEq a ρ rh ch ph τ pbh pbl →
        flexCC a ρ rh ph pbh pbl < benchCC a ρ rh pb) := by sorry
end BatteryLease.WinWin
