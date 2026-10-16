-- Prove2me | Theorems.Thm_BatteryLease_WinWin_proposition_5_i
-- name    : BatteryLease.WinWin.proposition_5_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:20:19.095055+00:00
-- url     : https://prove2.me/theorems/aad60499-6466-4703-8de1-078affc34c88
-- title:
--   Proposition 5 (first bullet), p. 17 — with Q^f_h > 0, capacity is smaller under flexible leasing iff ρ < 7a/(8+7a) and c_h ≤ T(r_h)
-- statement:
--   Under the standing assumptions, suppose $c_h<a(1-\rho)/2$ (so that $Q^f_h>0$), the benchmark interior conditions of Proposition 1 hold ($X-\rho<c_h<X+\rho$ with $X=(1-\rho)(2ar_h-r_h^2)/(2a)$, and $\tau^b<r_h$), and the flexible interior conditions of Proposition 2 hold ($\tfrac12(a+c_h/(1-\rho))\le r_h$ and $\tau^f<r_h$). Put
--   $$T(r_h)=\frac{(1-\rho)\big[(16ar_h-a^2-8r_h^2)(1-\rho)-8a\rho\big]}{14a(1-\rho)-16\rho}.$$
--   Then for every benchmark optimum and every flexible-leasing equilibrium,
--   $$BT^f\le BT^b\iff \rho<\frac{7a}{8+7a}\ \text{ and }\ c_h\le T(r_h),$$
--   where $BT^b=(1-\tau^b)r_h$ and $BT^f=(1-\tau^f+Q^f_h)r_h$ are the total battery capacities.
--
--   Total battery capacity is the third quantity in the win-win-win of Proposition 6.
--
--   **Formalization Note** "Smaller" is read as $\le$, as in the proof (Online Appendix p. 7: "$BT^f\le BT^b\iff\tau^f-Q^f_h\ge\tau^b$, which holds if and only if …"); equality occurs at $c_h=T(r_h)$. The interior conditions are those of Propositions 1 and 2. When $\rho\ge7a/(8+7a)$ the right side is false whatever value Lean assigns to $T$ (its denominator is positive exactly when $\rho<7a/(8+7a)$).
-- source:
--   Shi, Hu, Battery as a Service: Flexible Electric Vehicle Battery Leasing, M&SOM (2024), doi:10.1287/msom.2022.0587, authors' manuscript of 13 January 2024, p. 17, Proposition 5 (first bullet); proof Online Appendix p. 7 (PDF 39)

import Mathlib
import Definitions.Def_BatteryLease_WinWin_Setting

namespace BatteryLease.WinWin
theorem proposition_5_i (a ρ rh ch : ℝ) (hS : Standing a ρ rh ch)
    (hc : ch < a * (1 - ρ) / 2)
    (hlo : (1 - ρ) * (2 * a * rh - rh ^ 2) / (2 * a) - ρ < ch)
    (hhi : ch < (1 - ρ) * (2 * a * rh - rh ^ 2) / (2 * a) + ρ)
    (hτbr : ((1 - ρ) * rh ^ 2 + 2 * a * (ch - (1 - ρ) * rh + ρ)) / (4 * a * ρ) < rh)
    (hr1 : (a + ch / (1 - ρ)) / 2 ≤ rh)
    (hτfr : (2 * ch + ρ * (8 + a) - a) / (16 * ρ) < rh) :
    ∀ pb, IsBenchOpt a ρ rh ch pb → ∀ ph τ pbh pbl, IsFlexEq a ρ rh ch ph τ pbh pbl →
      (flexCap a rh τ ph pbh pbl ≤ benchCap a ρ rh pb ↔
        ρ < 7 * a / (8 + 7 * a) ∧
        ch ≤ (1 - ρ) * ((16 * a * rh - a ^ 2 - 8 * rh ^ 2) * (1 - ρ) - 8 * a * ρ) /
          (14 * a * (1 - ρ) - 16 * ρ)) := by sorry
end BatteryLease.WinWin
