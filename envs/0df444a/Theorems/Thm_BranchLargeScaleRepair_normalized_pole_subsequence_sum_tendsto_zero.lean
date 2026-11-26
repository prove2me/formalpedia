-- Prove2me | Theorems.Thm_BranchLargeScaleRepair_normalized_pole_subsequence_sum_tendsto_zero
-- name    : BranchLargeScaleRepair.normalized_pole_subsequence_sum_tendsto_zero
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-17T17:40:28.519142+00:00
-- url     : https://prove2.me/theorems/35c28087-462f-418d-b4f2-283c3af10226
-- title:
--   Large-scale decay of a complex pole sum with variable exponents
-- statement:
--   Let I be an index set and let z_i be complex numbers with d_i=Re(z_i)>0 and
--   \[\sum_{i\in I}d_i^{-2}<\infty.\]
--   Let X_j>0 and let k_j be nonnegative integers, with k_j>=2 for all sufficiently large j and k_j/X_j tending to infinity. Then
--   \[\lim_{j\to\infty}\sum_{i\in I}\left(\frac{X_j}{X_j+z_i}\right)^{k_j}=0.\]
--   The variable exponents permit application along subsequences of spectral orders without identifying the exponent with the subsequence index. This abstract estimate does not itself instantiate a zeta-zero family or prove a branch exclusion.
-- source:
--   Desenvolvimento RH: dominated-convergence composition using the previously checked BranchEscapeRepair quadratic-binomial and uniform-ratio estimates (small_scale_positive_from_counts.lean, 2026-11-16), reproduced with complete proofs under a distinct namespace. Mathlib supplies the dominated convergence theorem for infinite sums. Motivated by the large-scale step in On the Infinitude of Off-Critical Zeros, section 3.2; no claim of novelty for dominated convergence or Bernoulli inequalities.

import Mathlib
open Filter Topology

theorem BranchLargeScaleRepair.normalized_pole_subsequence_sum_tendsto_zero {ι : Type*} (z : ι → ℂ)
    (hz : ∀ i, 0 < (z i).re) (hs : Summable (fun i => 1/((z i).re)^2))
    (k : ℕ → ℕ) (hk : ∀ᶠ n : ℕ in atTop, 2 ≤ k n)
    (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (hscale : Tendsto (fun (n : ℕ) => (k n : ℝ)/x n) atTop atTop) :
    Tendsto (fun (n : ℕ) => ∑' i, ((x n : ℂ)/((x n : ℂ)+z i))^(k n)) atTop (𝓝 0) := by sorry
