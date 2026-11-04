-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_cutoff_dense_below_ext
-- name    : AvramDividend.Classical.avram_p2_c_borel_cutoff_dense_below_ext
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:22:37.092225+00:00
-- url     : https://prove2.me/theorems/d9a2fe78-f227-4be2-bf46-e71d663ffacb
-- title:
--   Cutoff Borel measure equality from dense tests below cutoff and one total-mass test
-- statement:
--   To identify Borel measures restricted below a fixed finite cutoff c, it suffices to compare their lower-halfline masses only at a dense family of thresholds strictly below c, together with the single total mass at cutoff c. Values at dense test thresholds above the cutoff automatically reduce to the total mass. Both restricted measures have finite mass.
-- source:
--   Proved cutoff dense-halfline extensionality (3f7566ae), splitting each threshold by a<c. This sharpens the analytic testing interface for the P2-A original rate and the P2-D Borel extension.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_cutoff_dense_halfline_ext
open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_cutoff_dense_below_ext
    (μ ν : Measure ℝ) (c : ℝ)
    (hμfin : μ (Iic c) ≠ ⊤) (hνfin : ν (Iic c) ≠ ⊤)
    (D : Set ℝ) (hDense : Dense D)
    (hCut : μ (Iic c) = ν (Iic c))
    (hTests : ∀ a : ℝ, a ∈ D → a < c → μ (Iic a) = ν (Iic a)) :
    μ.restrict (Iic c) = ν.restrict (Iic c) := by sorry
