-- Prove2me | Theorems.Thm_AlgebraicGeometry_finite_appTop_of_isProper_of_isNoetherianRing
-- name    : AlgebraicGeometry.finite_appTop_of_isProper_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/0ec3876a-5e92-582c-ab28-0f8e69c34282
-- title:
--   Global sections of a proper scheme are a finite A-module
-- statement:
--   Let $A$ be a commutative ring that is Noetherian, let $P$ be a scheme (in the universe of the ambient ring), and let $q\colon P\to\operatorname{Spec}A$ be a morphism of schemes, where the target is the spectrum of the commutative ring $A$ viewed as an object of the category of commutative rings, and assume that $q$ is proper. The assertion is that the ring homomorphism induced by $q$ on global sections, namely `q.appTop`, whose source is the ring of global sections of the structure sheaf of $\operatorname{Spec}A$ (canonically $A$ itself) and whose target is $\Gamma(P,\mathcal O_P)$, is a finite ring homomorphism: that is, $\Gamma(P,\mathcal O_P)$ is a finitely generated module over $A$ through this map. No coherence or flatness hypothesis beyond properness and Noetherianity of the base is imposed, and nothing is asserted about higher cohomology.
--
--   This is the degree-zero case of the finiteness theorem for the cohomology of coherent sheaves under a proper morphism over a locally Noetherian base (EGA III, Théorème 3.2.1, applied to $\mathcal F=\mathcal O_P$), specialised to an affine Noetherian base. It underlies the later analysis of proper morphisms in this development, being used for the comparison of global sections after base change to a fraction field or a residue field and for the production of clopen pieces of a proper fibre over a Henselian local ring; the proof invokes the finiteness of the alternating Čech complex of the structure sheaf on an ordered affine open cover, [`AlgebraicGeometry.OModulePresheaf.cechFinite_unit_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinite_unit_of_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_finite_appTop_of_isProper_of_isNoetherianRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicGeometry

universe u

theorem AlgebraicGeometry.finite_appTop_of_isProper_of_isNoetherianRing
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q] :
    q.appTop.hom.Finite := by sorry
