-- Prove2me | Theorems.Thm_BatteryLease_WinWin_lemma_3
-- name    : BatteryLease.WinWin.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:20:16.885983+00:00
-- url     : https://prove2.me/theorems/424bc685-8c68-4806-95a8-d70c73da732d
-- title:
--   Lemma 3, p. 13 — optimal peak up/downgrade rates, acquisition Q^f_h and peak profit (regime Q^f_h > 0)
-- statement:
--   Under the standing assumptions, fix $p_h\in\mathbb R$ and a low-capacity lease volume $\tau$ with $0<\tau<1$ and $\tau>c_h/(a(1-\rho))$. Suppose $\tfrac12(a+c_h/(1-\rho))\le r_h$ and $c_h/(2-2\rho)\le r_h$. Then the rates
--   $$\bar p^f_h=\frac{a+c_h/(1-\rho)}{2},\qquad \bar p^f_l=p_h-\frac{c_h}{2-2\rho}$$
--   satisfy $\bar p^f_h\le a$, $p_h-a\le\bar p^f_l\le p_h$, maximize the peak-period objective (1) over all rates with $\bar p_h\le a$, $p_h-a\le\bar p_l\le p_h$, and at them
--   $$Q^f_h=\frac{\tau-c_h/(a(1-\rho))}{2},\qquad (1)=\frac{c_h^2/(a(1-\rho)^2)+a\tau-2\tau c_h/(1-\rho)+4(1-\tau)p_h}{4}.$$
--
--   This solves the last stage of the flexible-leasing game; its value feeds the regular-period problem (2).
--
--   **Formalization Note** The page states the lemma for every $\tau$. Its $Q^f_h$ is negative when $\tau<c_h/(a(1-\rho))$, and there the optimum is a different (balanced) one, so the regime $\tau>c_h/(a(1-\rho))$ is a hypothesis. The two bounds by $r_h$ keep the optimal rates in the range where Lemma 2's interior formulas hold (the second is implied by the first and is kept for readability). The objective (1) is evaluated with the Table-1 volumes.
-- source:
--   Shi, Hu, Battery as a Service: Flexible Electric Vehicle Battery Leasing, M&SOM (2024), doi:10.1287/msom.2022.0587, authors' manuscript of 13 January 2024, p. 13, Lemma 3 and (1); proof Online Appendix p. 3 (PDF 35)

import Mathlib
import Definitions.Def_BatteryLease_WinWin_Setting

namespace BatteryLease.WinWin
theorem lemma_3 (a ρ rh ch τ ph : ℝ) (hS : Standing a ρ rh ch)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hQ : ch / (a * (1 - ρ)) < τ)
    (hr1 : (a + ch / (1 - ρ)) / 2 ≤ rh) (hr2 : ch / (2 - 2 * ρ) ≤ rh) :
    RateFeasible a ph ((a + ch / (1 - ρ)) / 2) (ph - ch / (2 - 2 * ρ)) ∧
    (∀ q r : ℝ, RateFeasible a ph q r →
      peakObj a ρ rh ch τ ph q r ≤
        peakObj a ρ rh ch τ ph ((a + ch / (1 - ρ)) / 2) (ph - ch / (2 - 2 * ρ))) ∧
    acq a rh τ ph ((a + ch / (1 - ρ)) / 2) (ph - ch / (2 - 2 * ρ)) =
      (τ - ch / (a * (1 - ρ))) / 2 ∧
    peakObj a ρ rh ch τ ph ((a + ch / (1 - ρ)) / 2) (ph - ch / (2 - 2 * ρ)) =
      (ch ^ 2 / (a * (1 - ρ) ^ 2) + a * τ - 2 * τ * ch / (1 - ρ) + 4 * (1 - τ) * ph) / 4 := by sorry
end BatteryLease.WinWin
