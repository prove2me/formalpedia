-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_truncated_convolution_prod_integrable_two_L1
-- name    : AvramDividend.Classical.causal_l1_truncated_convolution_prod_integrable_two_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T19:58:22.117982+00:00
-- url     : https://prove2.me/theorems/48fb7665-ab35-4865-baf8-4b4fac575503
-- title:
--   Finite-horizon causal convolution product is integrable for two L1 inputs
-- statement:
--   Two real kernels, each integrable on their respective positive and bounded causal intervals, yield an integrable product-measure convolution integrand. This extends the proved continuous-input lemma and supplies Fubini for signed L1 Gaussian Neumann power kernels.
-- source:
--   Generalise the Proved causal_l1_truncated_convolution_prod_integrable by replacing the continuous input hypothesis with its sole use, IntegrableOn g (Ioc 0 x). Apply integrable_indicator_iff and pinned Integrable.convolution_integrand.

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set

theorem AvramDividend.Classical.causal_l1_truncated_convolution_prod_integrable_two_L1
    (K g : ℝ → ℝ) (x : ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : IntegrableOn g (Ioc (0 : ℝ) x) volume) :
    Integrable (fun p : ℝ × ℝ =>
      ((Ioi (0 : ℝ)).indicator K) p.2 *
      ((Ioc (0 : ℝ) x).indicator g) (p.1 - p.2))
      (volume.prod volume) := by sorry
