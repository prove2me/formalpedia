-- Prove2me | Theorems.Thm_AlgebraicGeometry_specMap_comp_pullbackLift_eq_pullbackLift_comp_pullbackMap_of_comp_eq_comp
-- name    : AlgebraicGeometry.specMap_comp_pullbackLift_eq_pullbackLift_comp_pullbackMap_of_comp_eq_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/fc4f1f47-0542-5627-b42e-503d2e876c2b
-- title:
--   Equivariance of a pullback lift under an intertwined endomorphism
-- statement:
--   Let $g\colon G\to S$ be a morphism of schemes, and let $k$, $L$, $A$ be commutative rings (in the same universe). One is given a morphism $s\colon \operatorname{Spec} k\to S$, a morphism $\iota\colon \operatorname{Spec} L\to G$, an endomorphism $E\colon G\to G$ with $E\circ g$ equal to $g$ (i.e. $E$ is a morphism over $S$, written in Lean as $E \gg g = g$), and a ring endomorphism $e\colon L\to L$ which intertwines $\iota$ with $E$, in the sense that $\operatorname{Spec}(e)\gg \iota = \iota \gg E$. One is further given ring homomorphisms $a\colon L\to A$ and $c\colon k\to A$ such that the square $(\operatorname{Spec}(a)\gg\iota)\gg g = \operatorname{Spec}(c)\gg s$ commutes, so that the two morphisms $\operatorname{Spec}(a)\gg\iota\colon \operatorname{Spec} A\to G$ and $\operatorname{Spec}(c)\colon \operatorname{Spec} A\to \operatorname{Spec} k$ induce a morphism $\ell\colon \operatorname{Spec} A\to G\times_S \operatorname{Spec} k$ via `pullback.lift`. Finally, let $e_A\colon A\to A$ be a ring endomorphism with $e_A\circ a = a\circ e$ and $e_A\circ c = c$. The conclusion is the commutation $\operatorname{Spec}(e_A)\gg \ell = \ell \gg (E\times_S \mathrm{id})$, where $E\times_S\mathrm{id}$ is the morphism `pullback.map g s g s E (𝟙 _) (𝟙 _)` of the pullback induced by $E$ on the first factor and the identities on $\operatorname{Spec} k$ and $S$.
--
--   This is the elementary compatibility showing that a lift into a fibre product $G\times_S\operatorname{Spec} k$ defined by an affine point is equivariant for an endomorphism of $G$ over $S$ once the endomorphism is intertwined at the level of rings. It is used when reading off the effect of an endomorphism of a group scheme (a Hecke operator, a diamond operator, or multiplication by $p$) on the geometric special fibre of a finite level of the Néron object, in the two statements about the lift associated with the ordinary idempotent that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_specMap_comp_pullbackLift_eq_pullbackLift_comp_pullbackMap_of_comp_eq_comp.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.specMap_comp_pullbackLift_eq_pullbackLift_comp_pullbackMap_of_comp_eq_comp
    {G S : Scheme.{u}} (g : G ⟶ S)
    {k L A : Type u} [CommRing k] [CommRing L] [CommRing A]
    (s : Spec (CommRingCat.of k) ⟶ S)
    (ι : Spec (CommRingCat.of L) ⟶ G)
    (E : G ⟶ G) (hE : E ≫ g = g)
    (e : L →+* L) (hι : Spec.map (CommRingCat.ofHom e) ≫ ι = ι ≫ E)
    (a : L →+* A) (c : k →+* A)
    (hsq : (Spec.map (CommRingCat.ofHom a) ≫ ι) ≫ g = Spec.map (CommRingCat.ofHom c) ≫ s)
    (eA : A →+* A) (hea : eA.comp a = a.comp e) (hec : eA.comp c = c) :
    Spec.map (CommRingCat.ofHom eA) ≫ pullback.lift (Spec.map (CommRingCat.ofHom a) ≫ ι) (Spec.map (CommRingCat.ofHom c)) hsq =
      pullback.lift (Spec.map (CommRingCat.ofHom a) ≫ ι) (Spec.map (CommRingCat.ofHom c)) hsq ≫
        pullback.map g s g s E (𝟙 _) (𝟙 _) (by rw [Category.comp_id]; exact hE.symm) (by rw [Category.comp_id, Category.id_comp]) := by sorry
