-- Prove2me | Theorems.Thm_FamousTheorems_p_series
-- name    : FamousTheorems.p_series
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T07:14:55.581167+00:00
-- url     : https://prove2.me/theorems/91784d1a-0a46-4706-ace4-fe2a1387cefb
-- title:
--   Convergence of the p-series
-- statement:
--   **Convergence of the $p$-series.**
--
--   For real $p$,
--   $$\sum_{n \ge 1} \frac{1}{n^p} \text{ converges} \iff p > 1.$$
--
--   The boundary case $p = 1$ is the harmonic series, which diverges — so the criterion is sharp
--   and the divergence is exactly as slow as it can be. The proof is Cauchy's condensation test,
--   comparing the sum with $\sum 2^k \cdot 2^{-kp}$, a geometric series with ratio $2^{1-p}$.
--
--   This is the standard comparison against which other series are tested, and the convergent
--   range $p>1$ is precisely the half-plane on which the Riemann zeta function is defined by its
--   series. The failure at $p=1$ is what makes the pole of $\zeta$ at $s=1$ — and with it the
--   infinitude of the primes and the prime number theorem — possible.
--
--   The real exponent (rather than integer) version matters: it is what allows comparison with
--   $n^{-1-\varepsilon}$ for arbitrarily small $\varepsilon$.
--
--   **Formalization note.** The exponent is a real number and `^` is `Real.rpow`, so the statement
--   covers non-integer $p$. The result is Mathlib's `Real.summable_one_div_nat_rpow`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests (docs/undergrad.yaml, docs/overview.yaml); formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u v

open Filter Set Topology DirectSum

theorem p_series {p : ℝ} : Summable (fun n => 1 / (n : ℝ) ^ p : ℕ → ℝ) ↔ 1 < p := by sorry

end FamousTheorems
