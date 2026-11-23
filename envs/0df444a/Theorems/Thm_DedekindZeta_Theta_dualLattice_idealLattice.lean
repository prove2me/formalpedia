-- Prove2me | Theorems.Thm_DedekindZeta_Theta_dualLattice_idealLattice
-- name    : DedekindZeta.Theta.dualLattice_idealLattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:13:23.500645+00:00
-- url     : https://prove2.me/theorems/a08eb033-0620-4aac-bb11-cdb440a7d66a
-- title:
--   Theta: dual Lattice ideal Lattice
-- statement:
--   **Dual lattice as a submodule equality, Hermitian Minkowski dual** (the standard treatment, corrected for the conjugation twist).
--   The inner-product dual lattice of `Λ(𝔞)` is the conjugate
--   `conjMink '' Λ((𝔞𝔡)⁻¹)`, written as the image submodule
--   `(idealLattice K (dualIdeal K 𝔞)).map (conjMink K)`; `conjMink` is an isometric
--   involution preserving covolume and the Gaussian sum, so the transformation law
--   is unaffected. The bridge
--   is `Submodule.mem_one` for `(1 : Submodule ℤ ℝ)` (its elements are the integer
--   multiples of `1`, i.e. `∃ k : ℤ, (k : ℝ) = r`), matching the `∃ k : ℤ, ⟪y,x⟫ = k`
--   condition of `dual_idealLattice`; the inner-product argument order already
--   agrees (`⟪y, x⟫` with `y` dual, `x ∈ Λ(𝔞)`).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L818-L834
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L818-L834

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.dualLattice_idealLattice (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) :
    PoissonSummation.dualLattice (idealLattice K (𝔞 : FractionalIdeal (𝓞 K)⁰ K))
      = (idealLattice K (dualIdeal K 𝔞)).map
          ((conjMink K).toLinearEquiv.restrictScalars ℤ).toLinearMap := by sorry
