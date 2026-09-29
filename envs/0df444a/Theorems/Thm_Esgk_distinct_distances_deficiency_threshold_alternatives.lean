-- Prove2me | Theorems.Thm_Esgk_distinct_distances_deficiency_threshold_alternatives
-- name    : Esgk.distinct_distances_deficiency_threshold_alternatives
-- status  : Open
-- author  : @mysticflounder
-- created : 2026-09-14T02:15:18.466115+00:00
-- url     : https://prove2.me/theorems/9ecb03b8-28ba-428a-8a0a-b8d5dfab3806
-- title:
--   Five deficiency-threshold branches for planar distinct distances
-- statement:
--   Let $P$ be an injectively indexed set of $n$ planar points in general position, let $D(P)$ be its number of distinct distances, and define the natural deficiency $\sigma$ by
--
--   $$
--   (n-1)+\sigma=3D(P),\qquad s=\sigma+1.
--   $$
--
--   There are absolute positive integers $T,C$ and a threshold $N$ such that, whenever $n\ge N$, at least one of the following holds:
--
--   1. $n\le3s$;
--   2. $n\le s^2$;
--   3. $n\le s$;
--   4. $n^2<128T s^7$;
--   5. $n\le32C s^5$.
--
--   The same $T,C,N$ work for every qualifying configuration. These are the exact circle, nonabsolute, small-deficiency, threshold-failure, and threshold-success branches of the N15 distance--Newton bootstrap.
-- source:
--   Certified ESGK n^(1/5) pen-and-paper proof, Sections 2 and 15--16, https://github.com/flound1129/esgk-on3/blob/8a4c11ac6083f1c5e354b1a2556eae086f4b3ee5/docs/results/esgk-n15-authoritative-consolidated-proof-audit-corrected-v2-2026-08-25.md; independent 43-obligation audit, https://github.com/flound1129/esgk-on3/blob/8a4c11ac6083f1c5e354b1a2556eae086f4b3ee5/docs/audits/esgk-n15-full-proof-skeptic-2026-09-13.md

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Esgk_Foundation

open EuclideanGeometry Filter

namespace Esgk

/-- The deficiency--Newton argument reaches one of five exact numerical branches. -/
theorem distinct_distances_deficiency_threshold_alternatives :
    ∃ T C : ℕ, 0 < T ∧ 0 < C ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ p : Config n,
          Function.Injective p →
          InGeneralPosition (Config.toFinset p) →
          ∃ σ : ℕ,
            (n - 1) + σ = 3 * distinctDistances (Config.toFinset p) ∧
            let s := σ + 1
            n ≤ 3 * s ∨ n ≤ s ^ 2 ∨ n ≤ s ∨
              n ^ 2 < 128 * T * s ^ 7 ∨ n ≤ 32 * C * s ^ 5 := by
  sorry

end Esgk
