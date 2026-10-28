-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_convolution_contDiffOn_one_of_monotone_C1_kernel
-- name    : AvramDividend.Classical.causal_convolution_contDiffOn_one_of_monotone_C1_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:07:15.895113+00:00
-- url     : https://prove2.me/theorems/df538b19-3214-472b-a34c-c964a375643e
-- title:
--   C1 smoothing of a positive-time causal convolution by a continuous monotone C1 kernel
-- statement:
--   A causal convolution of a function continuous on nonnegative times with a kernel that vanishes at zero, is continuous and monotone on nonnegative times, and is C1 on positive times is C1 at all positive times. The kernel derivative is locally integrable up to zero by monotonicity and the fundamental theorem of calculus. Differentiating the convolution yields the causal convolution with the kernel derivative; the would-be moving-endpoint term vanishes because g(0)=0. This deterministic lemma is the missing analytic bridge between the already-Proved unbounded two-discount scale-resolvent convolution identity and zero-discount C1 regularity, especially the Gaussian branch where positive-discount C1 is already Proved.
-- source:
--   Real-analysis differentiation of causal Volterra convolutions, local absolute continuity of a continuous monotone C1 kernel, and the already-Proved scale resolvent identity AvramDividend.Classical.unbounded_scale_resolvent_convolution. Research dossier docs/prove2me/avram_zero_discount_c1_regularity_20261025.md.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
open MeasureTheory Set

theorem AvramDividend.Classical.causal_convolution_contDiffOn_one_of_monotone_C1_kernel
    (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Ici (0 : ℝ)))
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hg0 : g 0 = 0)
    (hgmono : MonotoneOn g (Ici (0 : ℝ)))
    (hgC1 : ContDiffOn ℝ 1 g (Ioi (0 : ℝ))) :
    ContDiffOn ℝ 1
      (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
        f s * g (x - s) ∂volume) (Ioi (0 : ℝ)) := by sorry
