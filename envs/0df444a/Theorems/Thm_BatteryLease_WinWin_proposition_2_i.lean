-- Prove2me | Theorems.Thm_BatteryLease_WinWin_proposition_2_i
-- name    : BatteryLease.WinWin.proposition_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:20:16.296971+00:00
-- url     : https://prove2.me/theorems/1d8c6d56-ed86-41ba-a318-ea1aa39136d5
-- title:
--   Proposition 2 (first case), p. 14 — the flexible-leasing equilibrium for c_h < a(1−ρ)/2, with Q^f_h > 0
-- statement:
--   Under the standing assumptions, suppose $c_h<a(1-\rho)/2$, $\tfrac12(a+c_h/(1-\rho))\le r_h$ and $\tau^f<r_h$, where
--   $$\tau^f=\frac{2c_h+\rho(8+a)-a}{16\rho}.$$
--   Let
--   $$p^f_h=\frac{6c_h+5a(1-\rho)+8\rho}{16},\quad \bar p^f_h=\frac{a+c_h/(1-\rho)}{2},\quad \bar p^f_l=\frac{c_h\,(6-8/(1-\rho))+5a(1-\rho)+8\rho}{16}.$$
--   Then
--   1. $(p^f_h,\tau^f,\bar p^f_h,\bar p^f_l)$ is a flexible-leasing equilibrium;
--   2. every flexible-leasing equilibrium equals it;
--   3. its additional acquisition is
--   $$Q^f_h=\frac{a(1-\rho)(2c_h+\rho(8+a)-a)-16\rho c_h}{32a\rho(1-\rho)}>0.$$
--
--   This is the equilibrium on the side where the manufacturer buys extra high-capacity batteries; it is one half of the comparison in Propositions 4–6.
--
--   **Formalization Note** An equilibrium is a lease rate together with a continuation (optimal feasible peak rates and the rationally expected lease volume) whose total profit (2) is at least that of every continuation at every lease rate. The bounds by $r_h$ are interior conditions (Lemma 2 with $r_h$; the proof's indifferent customer below $r_h$). The page's second case ("Otherwise") is not stated: it is false on part of $c_h\ge a(1-\rho)/2$.
-- source:
--   Shi, Hu, Battery as a Service: Flexible Electric Vehicle Battery Leasing, M&SOM (2024), doi:10.1287/msom.2022.0587, authors' manuscript of 13 January 2024, p. 14, Proposition 2 (first case); proof Online Appendix p. 4 (PDF 36)

import Mathlib
import Definitions.Def_BatteryLease_WinWin_Setting

namespace BatteryLease.WinWin
theorem proposition_2_i (a ρ rh ch : ℝ) (hS : Standing a ρ rh ch)
    (hc : ch < a * (1 - ρ) / 2)
    (hr1 : (a + ch / (1 - ρ)) / 2 ≤ rh)
    (hτr : (2 * ch + ρ * (8 + a) - a) / (16 * ρ) < rh) :
    IsFlexEq a ρ rh ch ((6 * ch + 5 * a * (1 - ρ) + 8 * ρ) / 16)
      ((2 * ch + ρ * (8 + a) - a) / (16 * ρ)) ((a + ch / (1 - ρ)) / 2)
      ((ch * (6 - 8 / (1 - ρ)) + 5 * a * (1 - ρ) + 8 * ρ) / 16) ∧
    (∀ ph τ pbh pbl : ℝ, IsFlexEq a ρ rh ch ph τ pbh pbl →
      ph = (6 * ch + 5 * a * (1 - ρ) + 8 * ρ) / 16 ∧
      τ = (2 * ch + ρ * (8 + a) - a) / (16 * ρ) ∧
      pbh = (a + ch / (1 - ρ)) / 2 ∧
      pbl = (ch * (6 - 8 / (1 - ρ)) + 5 * a * (1 - ρ) + 8 * ρ) / 16) ∧
    acq a rh ((2 * ch + ρ * (8 + a) - a) / (16 * ρ)) ((6 * ch + 5 * a * (1 - ρ) + 8 * ρ) / 16)
        ((a + ch / (1 - ρ)) / 2) ((ch * (6 - 8 / (1 - ρ)) + 5 * a * (1 - ρ) + 8 * ρ) / 16) =
      (a * (1 - ρ) * (2 * ch + ρ * (8 + a) - a) - 16 * ρ * ch) / (32 * a * ρ * (1 - ρ)) ∧
    0 < (a * (1 - ρ) * (2 * ch + ρ * (8 + a) - a) - 16 * ρ * ch) / (32 * a * ρ * (1 - ρ)) := by sorry
end BatteryLease.WinWin
