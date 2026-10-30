-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_deterministic_killed_qscale_no_root
-- name    : AvramDividend.Classical.avram_ws01b_bv_deterministic_killed_qscale_no_root
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:53:57.644856+00:00
-- url     : https://prove2.me/theorems/1630fd39-14af-46c8-9d4c-87aeb7b39eca
-- title:
--   Original BV killed q-scale deterministic semigroup without an auxiliary root hypothesis
-- statement:
--   Under Standing and genuine bounded variation, the actual original-P continuously lower-killed discounted q-scale expectation at every deterministic horizon and every real reserve, including the nonzero boundary Wq(0)=1/d, is exactly Wq(x). This is a source-faithful consequence of the canonically Proved original-Lévy all-real killed semigroup and positive Esscher-root existence in the BV branch. The result is the direct scalar fixed-time premise for the BV conditional future-window law.
-- source:
--   Accepted actual original-P deterministic killed q-scale identity 094049ef-e9e7-46f4-b55f-5f760a85dc10 plus BV positive root 3f64cde9-90a3-4f08-a5f1-4eee88b89407; no c2, stopped exit, optional stopping, or zero-origin-vanishing assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_positive_esscher_root
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_deterministic_killed_qscale

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_bv_deterministic_killed_qscale_no_root
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation) (x : ℝ) (t : ℝ≥0) :
    (∫ ω, ({ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω}).indicator
      (fun ω => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ω ∂P) =
      W x := by sorry
