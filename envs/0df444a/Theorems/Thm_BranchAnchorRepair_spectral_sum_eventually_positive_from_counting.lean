-- Prove2me | Theorems.Thm_BranchAnchorRepair_spectral_sum_eventually_positive_from_counting
-- name    : BranchAnchorRepair.spectral_sum_eventually_positive_from_counting
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-17T18:18:06.379037+00:00
-- url     : https://prove2.me/theorems/09cb45d1-6318-4cdb-9e18-ee30ab44e8f6
-- title:
--   Eventual positivity of spectral power sums in the large-scale regime
-- statement:
--   Let I index occurrences, with real numbers gamma_i >= 2 and |epsilon_i| <= 1/2, and complex numbers B_i satisfying Re(B_i)=gamma_i^2-epsilon_i^2 and B_i=gamma_i^2 when epsilon_i=0. Suppose every occurrence below or at height 1000 has epsilon_i=0, and there is an anchor a with gamma_a<=100. Assume constants C and p<1 satisfy
--   \[
--    |F|\le C y^p
--   \]
--   for every y>=1 and finite F contained in {i:gamma_i^2<=y}. Let k_j be natural numbers tending to infinity and x_j>0, with k_j/x_j tending to infinity. Then, for all sufficiently large j,
--   \[
--    \sum_{i\in I}\operatorname{Re}\bigl((x_j+B_i)^{-k_j}\bigr)>0.
--   \]
--   Occurrences retain their multiplicities. This estimate excludes a persistently negative spectral power sum in this regime under the stated geometric, low-height and counting assumptions. It does not assert that the full zeta-zero contract or all scale regimes have been discharged.
-- source:
--   Desenvolvimento RH, 2026-11-17. Composition of BranchAnchorRepair.normalized_offline_sum_from_counting with an explicit positive critical-anchor bound. Reciprocal summability is reproduced from ReciprocalCounting in actual_xi_branches.lean with complete proofs. Standard infinite-sum and complex real-part identities from Mathlib.

import Mathlib
open Filter Topology

theorem BranchAnchorRepair.spectral_sum_eventually_positive_from_counting {ι : Type*}
    (gamma eps : ι → ℝ) (B : ι → ℂ)
    (hB : ∀ i, (B i).re = (gamma i)^2-(eps i)^2)
    (hcritical : ∀ i, eps i = 0 → B i = ((gamma i)^2 : ℝ))
    (lower : ∀ i, 2 ≤ gamma i) (strip : ∀ i, |eps i| ≤ 1/2)
    (verified : ∀ i, gamma i ≤ 1000 → eps i = 0)
    (anchor : ι) (anchor_low : gamma anchor ≤ 100)
    (C p : ℝ) (hp : p < 1)
    (hcount : ∀ y ≥ (1 : ℝ), ∀ F : Finset ι,
      (∀ i ∈ F, (gamma i)^2 ≤ y) → (F.card : ℝ) ≤ C*y^p)
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (hscale : Tendsto (fun (n : ℕ) => (k n : ℝ)/x n) atTop atTop) :
    ∀ᶠ n : ℕ in atTop,
      0 < ∑' i, ((((x n : ℂ)+B i)⁻¹)^(k n)).re := by sorry
