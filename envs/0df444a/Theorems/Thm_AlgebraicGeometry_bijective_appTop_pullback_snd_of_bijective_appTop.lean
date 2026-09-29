-- Prove2me | Theorems.Thm_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop
-- name    : AlgebraicGeometry.bijective_appTop_pullback_snd_of_bijective_appTop
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/4659636d-7e16-5a4b-b9d5-47d5a2c4c5ca
-- title:
--   Global sections remain constants after base change over a field
-- statement:
--   Let $k$ be a field and let $X$ be a scheme equipped with a morphism $fX : X \to \operatorname{Spec} k$, and assume the underlying topological space of $X$ is quasi-compact and quasi-separated. Assume further that the ring map $k \to \Gamma(X,\mathcal{O}_X)$ obtained by composing the inverse of the canonical isomorphism $\Gamma(\operatorname{Spec} k,\mathcal{O}) \cong k$ with the map $fX^{\sharp}$ on sections over the whole space (`fX.appTop`) is bijective, i.e. the only global functions on $X$ are the constants. Then for every commutative ring $A$ carrying a $k$-algebra structure, the analogous map for the base change of $X$ along $\operatorname{Spec} A \to \operatorname{Spec} k$ is again bijective: forming the fibre product of $fX$ with $\operatorname{Spec}$ of the structure morphism $k \to A$, the ring map
--   $$A \longrightarrow \Gamma\bigl(X \times_{\operatorname{Spec} k} \operatorname{Spec} A,\ \mathcal{O}\bigr)$$
--   given by the inverse of $\Gamma(\operatorname{Spec} A,\mathcal{O}) \cong A$ followed by the map on global sections induced by the second projection is bijective.
--
--   This is the statement that the condition $\Gamma(X,\mathcal{O}_X) = k$ is preserved under arbitrary base change of the base field, a consequence of flat base change for global sections (every module over a field being flat). It is used in the proof of the rigidity lemma for proper morphisms ([`AlgebraicGeometry.exists_eq_snd_comp_of_comp_eq_const_of_isProper`](thm.html#AlgebraicGeometry.exists_eq_snd_comp_of_comp_eq_const_of_isProper)), in the criterion for geometric irreducibility of proper smooth schemes, and in the corresponding statement for the fibre over the residue field of a point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem AlgebraicGeometry.bijective_appTop_pullback_snd_of_bijective_appTop
    {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [QuasiSeparatedSpace X]
    (hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom)
    (A : Type u) [CommRing A] [Algebra k A] :
    Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop).hom := by sorry
