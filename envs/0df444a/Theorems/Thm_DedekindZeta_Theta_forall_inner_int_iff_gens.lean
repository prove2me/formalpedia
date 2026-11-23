-- Prove2me | Theorems.Thm_DedekindZeta_Theta_forall_inner_int_iff_gens
-- name    : DedekindZeta.Theta.forall_inner_int_iff_gens
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:11:10.723939+00:00
-- url     : https://prove2.me/theorems/14a8dd82-866a-41c3-89dd-5f8e8e39ace4
-- title:
--   Theta: forall inner int iff gens
-- statement:
--   **Reduction to generators** of the dual-lattice integrality condition.
--   Since `inner ℝ y ·` is `ℤ`-linear and the integers are closed under `ℤ`-linear
--   combinations, the condition `⟪y, x⟫ ∈ ℤ` for *all* `x` in the lattice
--   `Λ(I) = span ℤ (eEmb '' I)` is equivalent to its holding only on the generators
--   `x = eEmb a`, `a ∈ I`. This is step 2(a) towards `dual_idealLattice`: it
--   removes the `span`/lattice quantifier so the remaining work is the
--   inner-product ↔ trace-form bridge on individual ideal elements.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L490-L517
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L490-L517

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.forall_inner_int_iff_gens (I : FractionalIdeal (𝓞 K)⁰ K)
    (y : minkowskiSpace K) :
    (∀ x ∈ idealLattice K I, ∃ k : ℤ, (inner ℝ y x : ℝ) = k) ↔
      ∀ a ∈ (I : Submodule (𝓞 K) K), ∃ k : ℤ,
        (inner ℝ y (eEmb K a) : ℝ) = k := by sorry
