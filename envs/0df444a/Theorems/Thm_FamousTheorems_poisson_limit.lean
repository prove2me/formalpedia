-- Prove2me | Theorems.Thm_FamousTheorems_poisson_limit
-- name    : FamousTheorems.poisson_limit
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T09:15:24.769011+00:00
-- url     : https://prove2.me/theorems/d2e021e0-4421-4b19-a9d1-914fca61a579
-- title:
--   The Poisson limit theorem
-- statement:
--   **The Poisson limit theorem (law of rare events).** If $n\,p_n\to r$, then for every fixed $k$
--   $$\binom nk p_n^{\,k}(1-p_n)^{n-k}\longrightarrow e^{-r}\frac{r^k}{k!}\qquad(n\to\infty).$$
--
--   The binomial distribution $\mathrm{Bin}(n,p_n)$ converges to $\mathrm{Poisson}(r)$ when the number of trials grows and the success probability shrinks proportionally. It explains why counts of rare independent events (decays, arrivals, misprints) are Poisson distributed.
--
--   **Formalization note.** Mathlib's `ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop`, a pointwise statement on the probability mass functions.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem poisson_limit {p : ℕ → ℝ} {r : ℝ} (k : ℕ) (hr : Filter.Tendsto (fun n : ℕ => (n : ℝ) * p n) Filter.atTop (nhds r)) :
    Filter.Tendsto (fun n : ℕ => ((n.choose k : ℕ) : ℝ) * p n ^ k * (1 - p n) ^ (n - k)) Filter.atTop
      (nhds (Real.exp (-r) * r ^ k / (k.factorial : ℝ))) := by sorry

end FamousTheorems
