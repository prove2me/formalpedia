-- Prove2me | Theorems.Thm_DedekindZeta_PoissonSummation_hasSum_fourier_product_of_summable
-- name    : DedekindZeta.PoissonSummation.hasSum_fourier_product_of_summable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:06:41.791799+00:00
-- url     : https://prove2.me/theorems/3b7068f6-3096-4c10-bdad-c617eb36bae8
-- title:
--   Poisson Summation: has Sum fourier product of summable
-- statement:
--   **Multidimensional Fourier inversion on the product torus** `(AddCircle 1)^d`.
--   If `F` is continuous and its product-character Fourier coefficients are
--   absolutely summable, then at every point `θ` the multidimensional Fourier series
--   `∑_n (∏ i, fourier (n i) (θ i)) • c n` reconstructs `F θ`. The synthesis
--   character is `∏ i, fourier (n i)` (dual to the conjugate analysis character of
--   `fourierCoeffProd`). Reuses `UnitAddTorus.hasSum_mFourier_series_apply_of_summable`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L860-L881
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L860-L881

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
set_option autoImplicit true
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace
open DedekindZeta DedekindZeta.PoissonSummation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
open UnitAddTorus ComplexConjugate
attribute [local instance] DedekindZeta.PoissonSummation._p2m_local_instance_c635516111_828
variable {d : ℕ}

theorem DedekindZeta.PoissonSummation.hasSum_fourier_product_of_summable
    {F : (Fin d → AddCircle (1 : ℝ)) → ℂ} (hF : Continuous F)
    (h : Summable (fun n : Fin d → ℤ => fourierCoeffProd F n))
    (θ : Fin d → AddCircle (1 : ℝ)) :
    HasSum (fun n : Fin d → ℤ => (∏ i, fourier (n i) (θ i)) • fourierCoeffProd F n)
      (F θ) := by sorry
