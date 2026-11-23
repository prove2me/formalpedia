-- Prove2me | Theorems.Thm_DedekindZeta_Theta_discreteTopology_idealLattice
-- name    : DedekindZeta.Theta.discreteTopology_idealLattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:54:04.431796+00:00
-- url     : https://prove2.me/theorems/1ce5a6ba-6681-48f0-bdf4-539d89141849
-- title:
--   Theta: discrete Topology ideal Lattice
-- statement:
--   `Λ(I)` is discrete in `minkowskiSpace K` for nonzero `I` (the standard treatment): it is the image of the mixed-space ideal lattice under `eEmbℝ`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L866-L869
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L866-L869

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.discreteTopology_idealLattice (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    DiscreteTopology (idealLattice K I) := by sorry
