-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b129_original_marked_finite_grid_cutoff_occupation_eventually_exact
-- name    : AvramDividend.Classical.avram_b129_original_marked_finite_grid_cutoff_occupation_eventually_exact
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:38:09.716106+00:00
-- url     : https://prove2.me/theorems/6ceecd01-d67d-44d4-8067-b53111e9dc83
-- title:
--   Original finite-grid marked-cell negative-cutoff occupancy eventually equals the exact physical source marked-grid set
-- statement:
--   For an arbitrary finite family of genuinely marked cells on the original spectrally negative Lévy sample path, let J(n) be the occupied negative-band cell subset at cutoff n. Assume J(n) is contained in the genuine physically marked set, is monotone across cutoffs and captures each cell whenever a physical source negative-band jump exists there. Authoritatively Proved B118 constructs one common original negative cutoff N which detects a genuine jump in every physical marked cell simultaneously. Thus J(N) equals exactly the physical marked set, and by monotonicity all subsequent J(n) are exactly equal too. This strengthens the original occupied-card bound to an eventual exact physical identity, without changing the source process or its random cell endpoints.
-- source:
--   Proved B118 original finite marked-grid one-cutoff capture and finite set monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b118_original_finite_physically_marked_cells_one_cutoff
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True original finite stopped-grid marked occupancy is exactly attained by one finite negative cutoff and all later cutoffs. -/

theorem AvramDividend.Classical.avram_b129_original_marked_finite_grid_cutoff_occupation_eventually_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (S : Finset ℕ) (s t : ℕ → ℝ≥0)
    (hMarked : ∀ i ∈ S, ∃ u : ℝ≥0,
      s i < u ∧ u ≤ t i ∧
        X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    (J : ℕ → Finset ℕ)
    (hJsub : ∀ n, J n ⊆ S)
    (hJmono : ∀ n m, n ≤ m → J n ⊆ J m)
    (hJcapture : ∀ (n : ℕ) (i : ℕ), i ∈ S →
      (∃ u : ℝ≥0, s i < u ∧ u ≤ t i ∧
        X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
            -(1 / ((n : ℝ) + 1))) → i ∈ J n) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → J n = S := by sorry
