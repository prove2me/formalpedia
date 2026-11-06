-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_pair_moment_from_disjoint_union_square
-- name    : AvramDividend.Classical.avram_p4_f3_original_pair_moment_from_disjoint_union_square
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T09:58:22.765434+00:00
-- url     : https://prove2.me/theorems/2a3d3cef-21e4-47de-b9bf-ae46122c43e9
-- title:
--   Original disjoint negative-band cross moment follows from physical union's Poisson square moment
-- statement:
--   For two real original-space disjoint-band count functions A and B with integrable squares and product, if their physical fixed-time second moments are r squared plus r, s squared plus s and their union count A+B has second moment (r+s) squared plus r+s, then the cross count moment is exactly r*s. In the original negative-jump setting the identities come from the original intrinsic counts, the exact factorial-count source and additivity on disjoint mark bands, not from an independent copy or equality-in-law substitution. This removes a specific algebraic barrier before constructing physical-grid cross-band isometry; each source premise still requires proof.
-- source:
--   Algebraic covariance extraction from exact original physical union count second moment and its two constituent square moments. It targets the missing cross-band pair moment input of public Proved finite-grid isometry a29d73c1, and the original intrinsic factorial moment support 0a13392f. The future application must prove count additivity, integrability and each source moment for the actual disjoint mark sets.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_pair_moment_from_disjoint_union_square
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (A B : Ω → ℝ) (r s : ℝ)
    (hA2 : Integrable (fun ω => (A ω) ^ 2) P)
    (hB2 : Integrable (fun ω => (B ω) ^ 2) P)
    (hAB : Integrable (fun ω => A ω * B ω) P)
    (hAmean : (∫ ω, (A ω) ^ 2 ∂P) = r ^ 2 + r)
    (hBmean : (∫ ω, (B ω) ^ 2 ∂P) = s ^ 2 + s)
    (hUnion : (∫ ω, (A ω + B ω) ^ 2 ∂P) =
      (r + s) ^ 2 + (r + s)) :
    (∫ ω, A ω * B ω ∂P) = r * s := by sorry
