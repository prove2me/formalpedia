-- Prove2me | Theorems.Thm_BatteryLease_WinWin_proposition_1
-- name    : BatteryLease.WinWin.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:20:14.121629+00:00
-- url     : https://prove2.me/theorems/a3a46fd5-3762-4a4a-9dd1-f0e12c584f8f
-- title:
--   Proposition 1, p. 11 — simple leasing: optimal p^b_h, maximized profit, τ^b and capacity (1−τ^b)r_h
-- statement:
--   Under the standing assumptions, let $X=(1-\rho)(2ar_h-r_h^2)/(2a)$ and suppose $X-\rho<c_h<X+\rho$ and $\tau^b<r_h$, where
--   $$p^b_h=\frac{(1-\rho)(2ar_h-r_h^2)+2a(c_h+\rho)}{4a},\qquad \tau^b=\frac{(1-\rho)r_h^2+2a(c_h-(1-\rho)r_h+\rho)}{4a\rho}.$$
--   Then $p^b_h$ is the unique lease rate maximizing the simple-leasing profit $(1-\tau^b(p_h))(p_h-c_h)$ over all $p_h\in\mathbb R$, and
--   1. the maximized profit is $\dfrac{[(1-\rho)(2ar_h-r_h^2)-2a(c_h-\rho)]^2}{16\rho a^2}$;
--   2. the low-capacity lease volume at $p^b_h$ is $\tau^b$;
--   3. the total battery capacity is $(1-\tau^b)r_h$.
--
--   This is the benchmark against which flexible leasing is compared in Propositions 4–6.
--
--   **Formalization Note** The range $X-\rho<c_h<X+\rho$ is the proof's own condition (Online Appendix p. 2, "otherwise all customers lease low- or high-capacity batteries"); it is equivalent to $0<\tau^b<1$. The condition $\tau^b<r_h$ keeps the indifferent customer below $r_h$ as in Lemma 1; it holds automatically when $r_h\ge1$. The total customer cost, which the paper says "is included in the proof", is not part of this statement.
-- source:
--   Shi, Hu, Battery as a Service: Flexible Electric Vehicle Battery Leasing, M&SOM (2024), doi:10.1287/msom.2022.0587, authors' manuscript of 13 January 2024, p. 11, Proposition 1; proof Online Appendix pp. 1–2 (PDF 33–34)

import Mathlib
import Definitions.Def_BatteryLease_WinWin_Setting

namespace BatteryLease.WinWin
theorem proposition_1 (a ρ rh ch : ℝ) (hS : Standing a ρ rh ch)
    (hlo : (1 - ρ) * (2 * a * rh - rh ^ 2) / (2 * a) - ρ < ch)
    (hhi : ch < (1 - ρ) * (2 * a * rh - rh ^ 2) / (2 * a) + ρ)
    (hτr : ((1 - ρ) * rh ^ 2 + 2 * a * (ch - (1 - ρ) * rh + ρ)) / (4 * a * ρ) < rh) :
    IsBenchOpt a ρ rh ch (((1 - ρ) * (2 * a * rh - rh ^ 2) + 2 * a * (ch + ρ)) / (4 * a)) ∧
    (∀ p : ℝ, IsBenchOpt a ρ rh ch p →
      p = ((1 - ρ) * (2 * a * rh - rh ^ 2) + 2 * a * (ch + ρ)) / (4 * a)) ∧
    benchProfit a ρ rh ch (((1 - ρ) * (2 * a * rh - rh ^ 2) + 2 * a * (ch + ρ)) / (4 * a)) =
      ((1 - ρ) * (2 * a * rh - rh ^ 2) - 2 * a * (ch - ρ)) ^ 2 / (16 * ρ * a ^ 2) ∧
    tauB a ρ rh (((1 - ρ) * (2 * a * rh - rh ^ 2) + 2 * a * (ch + ρ)) / (4 * a)) =
      ((1 - ρ) * rh ^ 2 + 2 * a * (ch - (1 - ρ) * rh + ρ)) / (4 * a * ρ) ∧
    benchCap a ρ rh (((1 - ρ) * (2 * a * rh - rh ^ 2) + 2 * a * (ch + ρ)) / (4 * a)) =
      (1 - ((1 - ρ) * rh ^ 2 + 2 * a * (ch - (1 - ρ) * rh + ρ)) / (4 * a * ρ)) * rh := by sorry
end BatteryLease.WinWin
