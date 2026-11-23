-- Prove2me | Theorems.Thm_DedekindZeta_Theta_A_x_symm_adjoint_gaussV
-- name    : DedekindZeta.Theta.A_x_symm_adjoint_gaussV
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:19:08.284366+00:00
-- url     : https://prove2.me/theorems/2b4ec717-05b9-4826-8c8d-423a1ab2e6df
-- title:
--   Theta: A x symm adjoint gauss V
-- statement:
--   **Inverse-adjoint of `A_x` acts like the `x⁻¹`-scaling on `gaussV`.** Since
--   `gaussV` depends only on the Minkowski norm `‖·‖`, and per place the adjoint of
--   multiplication-by-`x_w` is multiplication-by-`conj x_w` (modulus `|x_w|`, the
--   same as `x⁻¹_w = 1/x_w`), the inverse-adjoint `(A_x.symm)ᴴ` and the
--   `x⁻¹`-scaling `toMinkowski (x⁻¹ · (toMinkowski).symm ·)` agree under `gaussV`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1582-L1649
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1582-L1649

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.A_x_symm_adjoint_gaussV {x : mixedEmbedding.mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) (w : minkowskiSpace K) :
    gaussV K (ContinuousLinearMap.adjoint
        ((A_x K hx).symm : minkowskiSpace K →L[ℝ] minkowskiSpace K) w)
      = gaussV K (toMinkowski K (x⁻¹ * (toMinkowski K).symm w)) := by sorry
