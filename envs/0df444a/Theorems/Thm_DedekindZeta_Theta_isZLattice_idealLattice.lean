-- Prove2me | Theorems.Thm_DedekindZeta_Theta_isZLattice_idealLattice
-- name    : DedekindZeta.Theta.isZLattice_idealLattice
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:54:09.749447+00:00
-- url     : https://prove2.me/theorems/bbb9016a-7c2e-416e-933b-772353281f23
-- title:
--   Theta: is ZLattice ideal Lattice
-- statement:
--   `Λ(I)` is a full `ℤ`-lattice of `minkowskiSpace K` for nonzero `I`
--   (the standard treatment): the image of the mixed-space ideal lattice under the
--   linear iso `eEmbℝ`. This is what `tsum_eq_tsum_fourier` needs.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L874-L881
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L874-L881

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.isZLattice_idealLattice (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    [DiscreteTopology (idealLattice K I)] :
    IsZLattice ℝ (idealLattice K I) := by sorry
