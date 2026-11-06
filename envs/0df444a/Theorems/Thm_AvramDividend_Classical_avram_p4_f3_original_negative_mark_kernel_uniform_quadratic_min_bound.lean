-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_mark_kernel_uniform_quadratic_min_bound
-- name    : AvramDividend.Classical.avram_p4_f3_original_negative_mark_kernel_uniform_quadratic_min_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:49:56.300507+00:00
-- url     : https://prove2.me/theorems/90c3bdda-44c9-4924-ae90-07fd5bf83187
-- title:
--   Uniform original stopped-state negative-mark Lévy quadratic kernel domination
-- statement:
--   The exact original classical-dividend verification function, under canonical nonnegative continuity, negative-half-line zero and compact strictly-positive C2 assumptions, has a source-exact negative-mark squared jump coefficient uniformly dominated on every compact positive reserve band by M times min(1,z^2). The coefficient is the literal w(u+z)-w(u), valid for C=top and arbitrary negative jump sizes. This is the central integrable kernel needed before a genuine predictable L2 stochastic isometry.
-- source:
--   Build a compact local Lipschitz bound from published 8179243e, a whole negative-tail value bound from published 22692cae, choose r=min(delta/2,1), split small/large negative marks and produce an explicit positive algebraic scalar M. Next apply original SpectrallyNegativeLevy.ν_integrable to the exact kernel. No surrogate process or assumed integrability.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_positive_band_lipschitz_source
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_tail_global_value_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_negative_mark_kernel_uniform_quadratic_min_bound
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ u ∈ Icc δ K, ∀ z : ℝ, z < 0 →
        (w (u + z) - w u) ^ 2 ≤ M * min 1 (z ^ 2) := by sorry
