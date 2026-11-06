-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_ContDiffOn_compact_band_exists_lipschitz
-- name    : AvramDividend.Classical.avram_p3_2_original_ContDiffOn_compact_band_exists_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T08:30:19.220374+00:00
-- url     : https://prove2.me/theorems/a747d35f-58fe-4079-afd5-da046e7cfd6b
-- title:
--   Original C1 value candidate admits a uniform compact reserve-band Lipschitz constant
-- statement:
--   A real value function differentiable once continuously on an ambient domain has a finite nonnegative Lipschitz constant on every compact interval of reserves contained in that domain, including nonempty intervals approaching the original control cap through strict localisation. This supplies the bounded nonlinear jump-kernel estimate used for the true original Lévy process.
-- source:
--   Pinned Mathlib ContDiffOn.locallyLipschitzOn, LocallyLipschitzOn.exists_lipschitzOnWith_of_compact and LipschitzOnWith.dist_le_mul; restriction of source C1 hypothesis to the compact physical reserve band.

import Mathlib

open Set
noncomputable section

/-- A genuine original C1 candidate on an ambient domain is Lipschitz
on every compact reserve interval contained in that domain. -/

theorem AvramDividend.Classical.avram_p3_2_original_ContDiffOn_compact_band_exists_lipschitz
    (w : ℝ → ℝ) (U : Set ℝ)
    (hw : ContDiffOn ℝ 1 w U) (lo hi : ℝ)
    (hsub : Set.Icc lo hi ⊆ U) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi,
        |w x - w y| ≤ L * |x - y| := by sorry
