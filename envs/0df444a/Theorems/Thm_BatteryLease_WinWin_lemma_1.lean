-- Prove2me | Theorems.Thm_BatteryLease_WinWin_lemma_1
-- name    : BatteryLease.WinWin.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:20:11.085026+00:00
-- url     : https://prove2.me/theorems/d2cc7669-7fb2-42ee-9d43-9f9f5a1743b6
-- title:
--   Lemma 1, p. 11 — under simple leasing, customers with d above [2ap_h − (1−ρ)r_h(2a−r_h)]/[2aρ] lease high-capacity batteries
-- statement:
--   Consider simple battery leasing under the standing assumptions ($a>1$, $a/(2+a)<\rho<1$, $0<r_h\le a$, $0\le c_h\le(1-\rho)a$) at a lease rate $p_h$, and put
--   $$\tau_0=\frac{2ap_h-(1-\rho)r_h(2a-r_h)}{2a\rho}.$$
--   Suppose $0\le\tau_0\le1$ and $\tau_0<r_h$. Then a customer with regular need $d\in[0,1]$ leases a high-capacity battery if and only if $d>\tau_0$, and the low- and high-capacity lease volumes are
--   $$\tau^b(p_h)=\tau_0,\qquad 1-\tau^b(p_h)=\frac{2a(\rho-p_h)+(1-\rho)r_h(2a-r_h)}{2a\rho}.$$
--
--   This is the customers' best response in the benchmark; Proposition 1 optimizes the lease rate against it.
--
--   **Formalization Note** The conditions $0\le\tau_0\le1$ and $\tau_0<r_h$ are the proof's interior case (Online Appendix p. 1: the indifference must happen at $d<r_h$, otherwise all customers lease one type). They are stated explicitly because outside them the volume is $0$ or $1$, not $\tau_0$. The strict $\tau_0<r_h$ excludes the tie $\tau_0=r_h<1$, at which every $d>r_h$ is indifferent and leases low.
-- source:
--   Shi, Hu, Battery as a Service: Flexible Electric Vehicle Battery Leasing, M&SOM (2024), doi:10.1287/msom.2022.0587, authors' manuscript of 13 January 2024, p. 11, Lemma 1; proof Online Appendix p. 1 (PDF 33)

import Mathlib
import Definitions.Def_BatteryLease_WinWin_Setting

namespace BatteryLease.WinWin
theorem lemma_1 (a ρ rh ch ph : ℝ) (hS : Standing a ρ rh ch)
    (hτ0 : 0 ≤ (2 * a * ph - (1 - ρ) * rh * (2 * a - rh)) / (2 * a * ρ))
    (hτ1 : (2 * a * ph - (1 - ρ) * rh * (2 * a - rh)) / (2 * a * ρ) ≤ 1)
    (hτr : (2 * a * ph - (1 - ρ) * rh * (2 * a - rh)) / (2 * a * ρ) < rh) :
    (∀ d ∈ Set.Icc (0:ℝ) 1,
      ¬ benchLow a ρ rh ph d ↔ (2 * a * ph - (1 - ρ) * rh * (2 * a - rh)) / (2 * a * ρ) < d) ∧
    tauB a ρ rh ph = (2 * a * ph - (1 - ρ) * rh * (2 * a - rh)) / (2 * a * ρ) ∧
    1 - tauB a ρ rh ph = (2 * a * (ρ - ph) + (1 - ρ) * rh * (2 * a - rh)) / (2 * a * ρ) := by sorry
end BatteryLease.WinWin
