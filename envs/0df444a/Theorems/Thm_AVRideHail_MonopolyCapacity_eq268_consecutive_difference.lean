-- Prove2me | Theorems.Thm_AVRideHail_MonopolyCapacity_eq268_consecutive_difference
-- name    : AVRideHail.MonopolyCapacity.eq268_consecutive_difference
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:10:26.232636+00:00
-- url     : https://prove2.me/theorems/628c821d-eb81-4eab-981f-9e2c1237ac3e
-- title:
--   (268), p. 87 — Π(n_{K+1}) − Π(n_K) = (Σ_{i≥K+1} P(m_i)(w₀ − c_v) − c_f)(n_{K+1} − n_K)
-- statement:
--   Let $n_1 < n_2 < \dots < n_I$ be increasing breakpoints, $P(m_1), \dots, P(m_I)$ any real weights, and $w_0, c_v, c_f$ real numbers, and let
--   $$\Pi(N) = (w_0 - c_v) \sum_{i=1}^I P(m_i) \min\{N, n_i\} - c_f N$$
--   be the objective (20). Then for every $K$ with $K + 1 \le I$,
--   $$\Pi(n_{K+1}) - \Pi(n_K) = \Big(\sum_{i=K+1}^I P(m_i)(w_0 - c_v) - c_f\Big)\cdot (n_{K+1} - n_K).$$
--
--   This identity gives the sign of each step of the piecewise-linear objective between consecutive breakpoints, which is what locates the optimal capacity.
--
--   **Formalization Note.** The paper states (268) for the breakpoints $n_i = n^*_{HV,i}$; the statement here holds for any strictly increasing breakpoints, a generalization. Scenarios are 0-based (`Fin I`), and the page's pair $(K, K+1)$ is a pair of indices $k, k'$ with $k' = k + 1$; the sum $\sum_{i=K+1}^I$ runs over indices $\ge k'$.
-- source:
--   Lian & van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), p. 87, (268), App. E.1.3

import Mathlib
import Definitions.Def_AVRideHail_MonopolyCapacity_Model

namespace AVRideHail.MonopolyCapacity

theorem eq268_consecutive_difference (P : AVRideHail.PureHV.MarketParams) (cv cf : ℝ) (I : ℕ)
    (prob : Fin I → ℝ) (ns : Fin I → ℝ) (hns : StrictMono ns) (k k' : Fin I)
    (hkk' : k'.val = k.val + 1) :
    profit20 P cv cf prob ns (ns k') - profit20 P cv cf prob ns (ns k) =
      ((∑ j ∈ Finset.Ici k', prob j) * (P.w0 - cv) - cf) * (ns k' - ns k) := by sorry

end AVRideHail.MonopolyCapacity
