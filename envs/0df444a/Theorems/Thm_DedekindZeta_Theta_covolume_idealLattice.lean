-- Prove2me | Theorems.Thm_DedekindZeta_Theta_covolume_idealLattice
-- name    : DedekindZeta.Theta.covolume_idealLattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:19:52.594601+00:00
-- url     : https://prove2.me/theorems/082a28f6-6adf-4b4a-aa81-171fb3b9974e
-- title:
--   Theta: covolume ideal Lattice
-- statement:
--   **Covolume of the √2-weighted ideal lattice** (the standard treatment):
--   for a nonzero integral ideal `𝔞`, the Euclidean lattice `Λ(𝔞)` of
--   `DedekindZeta.Theta.idealLattice` (the image of `𝔞` under the `√2`-weighted
--   embedding `eEmb = toMinkowski ∘ mixedEmbedding`) has covolume exactly
--   `𝔑(𝔞)·√|d_K| = covolume K 𝔞`.
--
--   The `√2`-weighting contributes a Jacobian factor `2 ^ r₂` that cancels the
--   `(2⁻¹) ^ r₂` appearing in Mathlib's unweighted
--   `mixedEmbedding.covolume_idealLattice`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1988-L2053
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1988-L2053

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open MeasureTheory

theorem DedekindZeta.Theta.covolume_idealLattice (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) :
    ZLattice.covolume (idealLattice K (𝔞 : FractionalIdeal (𝓞 K)⁰ K))
      = covolume K 𝔞 := by sorry
