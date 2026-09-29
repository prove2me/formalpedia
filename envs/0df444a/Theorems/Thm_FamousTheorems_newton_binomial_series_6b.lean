-- Prove2me | Theorems.Thm_FamousTheorems_newton_binomial_series_6b
-- name    : FamousTheorems.newton_binomial_series_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:42:25.823584+00:00
-- url     : https://prove2.me/theorems/795a4eab-c0c3-4140-9c37-dc488447e5ee
-- title:
--   Newton's generalized binomial theorem (binomial series)
-- statement:
--   **Newton's generalized binomial theorem (binomial series).** For every complex exponent $a$,
--   $$(1+z)^a=\sum_{k=0}^\infty\binom ak z^k\qquad(|z|<1),$$
--   where $\binom ak=\frac{a(a-1)\cdots(a-k+1)}{k!}$ and $(1+z)^a$ is the principal power. The series converges on the open unit disc.
--
--   Newton found this series in 1665 for rational exponents. It extends the binomial theorem from positive integer exponents to arbitrary ones and was one of the first infinite series used systematically in analysis. It gives expansions such as $\sqrt{1+z}$ and $(1-z)^{-1/2}$ and is the Taylor series of $(1+z)^a$ at $0$.
--
--   **Formalization note.** Mathlib's `Complex.one_add_cpow_hasFPowerSeriesOnBall_zero`. `binomialSeries ℂ a` is the formal power series $\sum_k\binom ak z^k$, and `HasFPowerSeriesOnBall f P 0 1` says that it converges to $f$ on the open ball of radius $1$ about $0$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Complex.one_add_cpow_hasFPowerSeriesOnBall_zero`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem newton_binomial_series_6b (a : ℂ) : HasFPowerSeriesOnBall (fun x : ℂ => (1 + x) ^ a) (binomialSeries ℂ a) 0 1 := by sorry

end FamousTheorems
