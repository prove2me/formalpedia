-- Prove2me | Theorems.Thm_AlgebraicGeometry_mem_smoothLocus_iff_formallySmooth_of_ringEquiv_stalk
-- name    : AlgebraicGeometry.mem_smoothLocus_iff_formallySmooth_of_ringEquiv_stalk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/ed0a25f9-cce1-57cf-8fe2-afd84fdc3501
-- title:
--   Smooth locus membership via formal smoothness of a model of the stalk
-- statement:
--   Let $R$ be a commutative ring and let $f : X \to \operatorname{Spec} R$ be a morphism of schemes (in the zeroth universe) which is locally of finite presentation, and let $x$ be a point of $X$. Let $S$ be a commutative ring equipped with an $R$-algebra structure, and let $e : \mathcal{O}_{X,x} \xrightarrow{\ \sim\ } S$ be a ring isomorphism from the stalk of the structure sheaf of $X$ at $x$ onto $S$. The compatibility hypothesis is that for every $r \in R$, the element $e$ sends the germ at $x$ of the global section $f^{*}(r)$ — obtained by transporting $r$ through the inverse of the canonical isomorphism $R \cong \Gamma(\operatorname{Spec} R, \mathcal{O})$, applying the map on global sections induced by $f$, and taking the germ at $x$ — to $\operatorname{algebraMap}_{R,S}(r)$, i.e. $e$ is $R$-linear for the two $R$-algebra structures. The conclusion is the equivalence: $x$ belongs to the smooth locus of $f$, that is, the local homomorphism $\mathcal{O}_{\operatorname{Spec} R, f(x)} \to \mathcal{O}_{X,x}$ induced by $f$ on stalks is formally smooth, if and only if $S$ is formally smooth as an $R$-algebra.
--
--   This is the standard recognition criterion for the smooth locus of a morphism over an affine base: smoothness at $x$ may be tested as formal smoothness over $R$ of any concrete ring presenting the local ring $\mathcal{O}_{X,x}$ compatibly with the structure map. It is used wherever a local ring of a scheme over an affine base is identified with an explicit localisation, in particular in the analysis of normal models and Drinfeld charts of modular curves, where the smoothness clause of a local description is reduced to a statement about an explicit $R$-algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_mem_smoothLocus_iff_formallySmooth_of_ringEquiv_stalk.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.mem_smoothLocus_iff_formallySmooth_of_ringEquiv_stalk
    {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation f]
    (x : X) {S : Type} [CommRing S] [Algebra R S] (e : X.presheaf.stalk x ≃+* S)
    (he : ∀ r : R, e ((X.presheaf.germ ⊤ x trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) =
      algebraMap R S r) :
    x ∈ f.smoothLocus ↔ Algebra.FormallySmooth R S := by sorry
