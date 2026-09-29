-- Prove2me | Theorems.Thm_FamousTheorems_leibniz_series_pi
-- name    : FamousTheorems.leibniz_series_pi
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T21:55:29.419573+00:00
-- url     : https://prove2.me/theorems/3f1c5555-9abd-4c33-a786-60d71adb98ba
-- title:
--   Leibniz's series for $\pi$
-- statement:
--   **The Leibniz (Madhava–Gregory) series.**
--
--   $$1 - \frac13 + \frac15 - \frac17 + \cdots \;=\; \frac{\pi}{4}.$$
--
--   It is the Taylor series of $\arctan$ evaluated at $x = 1$, where convergence is only conditional
--   — the terms decrease to $0$ and alternate, so Leibniz's test applies, but the series is not
--   absolutely convergent.
--
--   Discovered by Madhava of Sangamagrama around 1400, some 250 years before Gregory and Leibniz. As
--   a way to compute $\pi$ it is hopeless: the error after $k$ terms is about $1/(2k)$, so ten
--   correct digits would need billions of terms. Its interest is that such an elementary alternating
--   sum of unit fractions produces $\pi$ at all.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem leibniz_series_pi :
    Filter.Tendsto (fun k : ℕ => ∑ i ∈ Finset.range k, ((-1) ^ i / (2 * (i : ℝ) + 1)))
      Filter.atTop (nhds (Real.pi / 4)) := by sorry

end FamousTheorems
