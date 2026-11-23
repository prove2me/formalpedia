-- Prove2me | Theorems.Thm_DedekindZeta_Theta_normAtPlace_conjMixed
-- name    : DedekindZeta.Theta.normAtPlace_conjMixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:21:20.8578+00:00
-- url     : https://prove2.me/theorems/7e281d7c-ae89-4bbf-bdd3-6235e6d1ffa9
-- title:
--   Theta: norm At Place conj Mixed
-- statement:
--   The Minkowski place-norm is invariant under the complex conjugation
--   `conjMixed` (real places are fixed; on complex places `‖conj z‖ = ‖z‖`).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L2188-L2193
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L2188-L2193

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.normAtPlace_conjMixed (w : InfinitePlace K) (ξ : mixedSpace K) :
    normAtPlace w (conjMixed K ξ) = normAtPlace w ξ := by sorry
