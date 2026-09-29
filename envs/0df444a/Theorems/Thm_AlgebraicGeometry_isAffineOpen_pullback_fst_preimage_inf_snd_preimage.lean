-- Prove2me | Theorems.Thm_AlgebraicGeometry_isAffineOpen_pullback_fst_preimage_inf_snd_preimage
-- name    : AlgebraicGeometry.isAffineOpen_pullback_fst_preimage_inf_snd_preimage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/04116ed5-5f7b-5d90-a777-03b112097206
-- title:
--   Product of affine opens is affine in a fibre product
-- statement:
--   Let $X$, $Y$, $S$ be schemes (in a fixed universe) with $S$ affine, and let $f : X \to S$ and $g : Y \to S$ be morphisms of schemes. Let $U$ be an open subset of $X$ which is an affine open, i.e. the scheme structure on $U$ induced from $X$ is affine, and let $V$ be an open subset of $Y$ which is likewise an affine open. The assertion is that the open subset of the fibre product $X \times_S Y$ obtained as the intersection of the preimage of $U$ under the first projection $\mathrm{pullback.fst}\ f\ g$ with the preimage of $V$ under the second projection $\mathrm{pullback.snd}\ f\ g$ — preimages and intersection being taken in the lattice of opens of $X \times_S Y$ — is again an affine open. Here the fibre product is the one furnished by the chosen pullback cone in the category of schemes, and the preimage operation $\cdot\ {}^{-1}\mathcal{U}\ \cdot$ is the action of a morphism of schemes on opens of its target.
--
--   This is the standard construction step in the existence of fibre products of schemes: over an affine base, the affine opens of the shape $p^{-1}(U) \cap q^{-1}(V)$ cover $X \times_S S Y$ and witness that it is covered by affine opens. Within the present development it is the first half of [`AlgebraicGeometry.isAffineOpen_pullback_fst_preimage_inf_snd_preimage_and_closure_eq_top`](thm.html#AlgebraicGeometry.isAffineOpen_pullback_fst_preimage_inf_snd_preimage_and_closure_eq_top), which in addition records a density statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isAffineOpen_pullback_fst_preimage_inf_snd_preimage.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

theorem AlgebraicGeometry.isAffineOpen_pullback_fst_preimage_inf_snd_preimage
    {X Y S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) (g : Y ⟶ S)
    {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V) :
    IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := by sorry
