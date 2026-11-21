-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_original_finitecap_gaussian_crossing_positive_spatial_L1
-- name    : AvramDividend.Classical.avram_a25_original_finitecap_gaussian_crossing_positive_spatial_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T09:59:36.655823+00:00
-- url     : https://prove2.me/theorems/384baa07-001b-4fa7-bcf2-c919390607d3
-- title:
--   Original finitecap true stopped Gaussian crossing positive spatial residual is integrable
-- statement:
--   Prove directly that the nonnegative part of the true caplinear Gaussian crossing spatial correction max(V(Y+R)−w(Y),0) is integrable for any original bounded postpayment reserve Y and integrable actual Gaussian stopped increment R, assuming physical value measurability. Derive from the accepted finitecap scalar crossing bound and the L1 spatial difference lemma. This is the positive crossing error notion required by the already proved fullcross error closure 850eb3de. No fictitious martingale or globally bounded value continuation.
-- source:
--   Finitecap physical Gaussian true stopped crossing positive-part integrability; one-cell source for original fullcross L1 estimates.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical

theorem AvramDividend.Classical.avram_a25_original_finitecap_gaussian_crossing_positive_spatial_L1
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    (w : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hw_cont : ContinuousOn w (Set.Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (Y R : Ω → ℝ) (hY : ∀ᵐ ω ∂P, 0 ≤ Y ω ∧ Y ω ≤ b)
    (hR : Integrable R P)
    (hMeas : AEStronglyMeasurable (fun ω =>
      (if Y ω + R ω ≤ b then w (Y ω + R ω)
       else w b + (Y ω + R ω - b)) - w (Y ω)) P) :
    Integrable (fun ω =>
      max ((if Y ω + R ω ≤ b then w (Y ω + R ω)
       else w b + (Y ω + R ω - b)) - w (Y ω)) 0) P := by sorry
