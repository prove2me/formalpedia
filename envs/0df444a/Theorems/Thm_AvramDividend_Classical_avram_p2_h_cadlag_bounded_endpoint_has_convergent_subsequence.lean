-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_bounded_endpoint_has_convergent_subsequence
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_bounded_endpoint_has_convergent_subsequence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:45:13.646806+00:00
-- url     : https://prove2.me/theorems/59b63b62-10ce-4bb1-a154-0a2fef5d9f9f
-- title:
--   Every bounded mesh endpoint sequence admits a convergent cofinal subsequence
-- statement:
--   Bolzano-Weierstrass on the compact NNReal interval [0,T] produces a strictly increasing subsequence of any bounded sequence of candidate mesh endpoints, converging to a time in that horizon.

import Mathlib

namespace AvramDividend.Classical
end AvramDividend.Classical

open Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_h_cadlag_bounded_endpoint_has_convergent_subsequence
    (T : ℝ≥0) (b : ℕ → ℝ≥0)
    (hb : ∀ n, b n ≤ T) :
    ∃ t : ℝ≥0, t ≤ T ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (b ∘ φ) atTop (𝓝 t) := by sorry
