-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_triangle_fubini
-- name    : AvramDividend.Classical.causal_l1_kernel_triangle_fubini
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T17:39:58.165874+00:00
-- url     : https://prove2.me/theorems/9d543682-7b78-4bf0-a5c5-eb9452a4c1e6
-- title:
--   Fubini identity for causal convolution and the primitive of a continuous input
-- statement:
--   Let K be integrable on strictly positive times and g continuous on nonnegative times. For x>0, integrating the causal convolution K*g over (0,x] equals the convolution of K with the primitive G(s)=∫_0^s g(t)dt. Use Fubini on the finite triangle 0≤s≤t≤x. Both sides reduce to ∫_0^x g(r) (∫_0^(x-r) K(u)du)dr after swapping integration and affine substitutions. Compact boundedness of g and positive-side L1-integrability of K justify the exchanges.
-- source:
--   Fubini/Tonelli on a finite triangular domain and translation/reflection invariance of Lebesgue integration; see FUBINI_PROOF_ROUTE.md in the source artefact directory.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_l1_kernel_triangle_fubini
    (K g : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (x : ℝ) (hx : 0 < x) :
    (∫ t in Ioc (0 : ℝ) x,
      (∫ s in Ioc (0 : ℝ) t, K (t - s) * g s ∂volume) ∂volume) =
    (∫ s in Ioc (0 : ℝ) x,
      K (x - s) * (∫ t in Ioc (0 : ℝ) s, g t ∂volume) ∂volume) := by sorry
