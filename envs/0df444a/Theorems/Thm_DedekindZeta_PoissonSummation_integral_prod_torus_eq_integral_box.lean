-- Prove2me | Theorems.Thm_DedekindZeta_PoissonSummation_integral_prod_torus_eq_integral_box
-- name    : DedekindZeta.PoissonSummation.integral_prod_torus_eq_integral_box
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:06:55.605799+00:00
-- url     : https://prove2.me/theorems/31bb38d4-b18a-4489-a1a0-ff774836bd15
-- title:
--   Poisson Summation: integral prod torus eq integral box
-- statement:
--   **Step 1: product torus = unit box.** Writing the coordinatewise quotient
--   `red : (Fin d → ℝ) → (Fin d → AddCircle 1)`, `red y i = (y i : AddCircle 1)`,
--   the mass-1 Haar integral over the product torus equals the Lebesgue integral of
--   `g ∘ red` over the half-open unit box `(Ioc 0 1)^d`. This is Fubini for
--   `Measure.pi` together with the one-variable identity relating
--   `∫ t : AddCircle 1, h t` to `∫ t in Ioc 0 1, h t` (period `1`, unit mass).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L932-L946
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L932-L946

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
set_option autoImplicit true
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace
open DedekindZeta DedekindZeta.PoissonSummation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
open UnitAddTorus
attribute [local instance] DedekindZeta.PoissonSummation._p2m_local_instance_c635516111_908
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
variable {d : ℕ} (b : Basis (Fin d) ℤ L)

theorem DedekindZeta.PoissonSummation.integral_prod_torus_eq_integral_box
    {g : (Fin d → AddCircle (1 : ℝ)) → ℂ} (hg : Integrable g) :
    (∫ θ, g θ)
      = ∫ y in Set.univ.pi (fun _ : Fin d => Set.Ioc (0 : ℝ) 1),
          g (fun i => ((y i : ℝ) : AddCircle (1 : ℝ))) := by sorry
