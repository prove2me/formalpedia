-- Prove2me | Theorems.Thm_DedekindZeta_Theta_idealLattice_eq_comap
-- name    : DedekindZeta.Theta.idealLattice_eq_comap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:54:10.819095+00:00
-- url     : https://prove2.me/theorems/9ff9061e-567f-4718-9b6c-7e48992a015d
-- title:
--   Theta: ideal Lattice eq comap
-- statement:
--   The Minkowski ideal lattice `Λ(I)` is the image of the mixed-space ideal
--   lattice `mixedEmbedding.idealLattice K I'` under the linear iso `eEmbℝ`,
--   phrased as a `ZLattice.comap` along `eEmbℝ.symm` so the `instIsZLatticeComap`
--   instance applies. For `v : minkowskiSpace K`, `v ∈ Λ(I)` iff its preimage
--   `eEmbℝ.symm v` lies in the mixed-space lattice (both reduce to `∃ a ∈ I, …`).
--   the standard treatment: `Λ(I)` is a full discrete lattice.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L842-L863
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L842-L863

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.idealLattice_eq_comap (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    idealLattice K I =
      ZLattice.comap ℝ (mixedEmbedding.idealLattice K (Units.mk0 I hI))
        (eEmbℝ K).symm.toLinearMap := by sorry
