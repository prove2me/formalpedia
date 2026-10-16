-- Prove2me | Theorems.Thm_BatteryLease_WinWin_lemma_4
-- name    : BatteryLease.WinWin.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:20:20.873902+00:00
-- url     : https://prove2.me/theorems/a322ab94-c8e7-44a3-aae8-2b234f7f3a56
-- title:
--   Lemma 4, p. 14 — flexible lease volume τ = [8p_h − 3a(1−ρ) − 2c_h]/[8ρ] under Lemma 3's anticipated rates
-- statement:
--   Under the standing assumptions, let customers anticipate Lemma 3's rates $\bar p_h=\tfrac12(a+c_h/(1-\rho))$ and $\bar p_l=p_h-c_h/(2-2\rho)$, with $\tfrac12(a+c_h/(1-\rho))\le r_h$ and $c_h/(2-2\rho)\le r_h$. Put
--   $$\tau=\frac{8p_h-3a(1-\rho)-2c_h}{8\rho}$$
--   and suppose $0\le\tau\le1$ and $\tau<r_h$. Then the low- and high-capacity lease volumes under flexible leasing are $\tau$ and
--   $$1-\tau=\frac{8\rho+3a(1-\rho)+2c_h-8p_h}{8\rho}.$$
--
--   This is the customers' regular-period response to the lease rate once the peak period is solved; Proposition 2 optimizes $p_h$ against it.
--
--   **Formalization Note** The page's "given $p_h$" means given $p_h$ and the rates of Lemma 3 that customers anticipate (p. 13: the peak results are carried into the regular period as functions of $\tau$ and $p_h$). The bounds $0\le\tau\le1$ and $\tau<r_h$ are the proof's interior case (Online Appendix pp. 3–4: the indifference happens at $d<r_h$).
-- source:
--   Shi, Hu, Battery as a Service: Flexible Electric Vehicle Battery Leasing, M&SOM (2024), doi:10.1287/msom.2022.0587, authors' manuscript of 13 January 2024, p. 14, Lemma 4; proof Online Appendix pp. 3–4 (PDF 35–36)

import Mathlib
import Definitions.Def_BatteryLease_WinWin_Setting

namespace BatteryLease.WinWin
theorem lemma_4 (a ρ rh ch ph : ℝ) (hS : Standing a ρ rh ch)
    (hr1 : (a + ch / (1 - ρ)) / 2 ≤ rh) (hr2 : ch / (2 - 2 * ρ) ≤ rh)
    (hτ0 : 0 ≤ (8 * ph - 3 * a * (1 - ρ) - 2 * ch) / (8 * ρ))
    (hτ1 : (8 * ph - 3 * a * (1 - ρ) - 2 * ch) / (8 * ρ) ≤ 1)
    (hτr : (8 * ph - 3 * a * (1 - ρ) - 2 * ch) / (8 * ρ) < rh) :
    tauF a ρ rh ph ((a + ch / (1 - ρ)) / 2) (ph - ch / (2 - 2 * ρ)) =
      (8 * ph - 3 * a * (1 - ρ) - 2 * ch) / (8 * ρ) ∧
    1 - tauF a ρ rh ph ((a + ch / (1 - ρ)) / 2) (ph - ch / (2 - 2 * ρ)) =
      (8 * ρ + 3 * a * (1 - ρ) + 2 * ch - 8 * ph) / (8 * ρ) := by sorry
end BatteryLease.WinWin
