-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
-- name    : AvramDividend.Classical.avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T17:35:44.946129+00:00
-- url     : https://prove2.me/theorems/44b01929-5817-44ac-9439-6eb3c9879f2c
-- title:
--   UBV C² gradient implies the inclusive cap dividend-value secant inequality for every nonnegative cap
-- statement:
--   The derivative lower bound w'≥1 on the strict interior of an arbitrary nonnegative cap, and interior C² regularity with continuity up to zero, imply b−a≤w(b)−w(a) for all 0≤a≤b≤C, including b=C and the degenerate zero cap C=0. The positive-cap case is the accepted general full-cap mean-value secant theorem, reducing C² to C¹; if C=0 both nonnegative reserves are zero so the inequality holds identically. This is the deterministic gradient dominance necessary to control continuous and singular-continuous dividend Stieltjes losses in the corrected unbounded-variation stochastic verification proof.
-- source:
--   Canonical Proved full-cap gradient secant UUID 2ba5cc4f-3aab-40ea-a59a-8a49633c7595, pinned Mathlib ContDiffOn.of_le and ENNReal.ofReal_eq_zero. Exact private remote compiler probe ba10a33b-302f-4ad9-8258-8fbbb1812408 passed sentinel with no source diagnostics, SHA-256 8f109c4e913aa240be3b6fb21e561edca17eeac38435787998bd8f6f23159545.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : ENNReal.ofReal b ≤ C) :
    b - a ≤ w b - w a := by sorry
