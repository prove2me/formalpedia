-- Prove2me | Theorems.Thm_AlgebraicGeometry_forall_irreducibleSpace_pullback_iff_geometricallyIrreducible_fiberToSpecResidueField
-- name    : AlgebraicGeometry.forall_irreducibleSpace_pullback_iff_geometricallyIrreducible_fiberToSpecResidueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/2bc95030-5669-5b00-9583-6cf75d24a276
-- title:
--   Irreducibility of all geometric fibres over s equals geometric irreducibility of the fibre
-- statement:
--   Let $S$ be a commutative ring, let $Z$ be a scheme, let $f \colon Z \to \operatorname{Spec} S$ be a morphism of schemes, and let $s$ be a point of $\operatorname{Spec} S$, i.e. a prime ideal $s.\mathrm{asIdeal}$ of $S$. The assertion is an equivalence between the following two statements. First: for every field $k$ in the ambient universe which is algebraically closed and every ring homomorphism $x \colon S \to k$ whose kernel equals $s.\mathrm{asIdeal}$, the underlying topological space of the pullback of $f$ along $\operatorname{Spec}$ of $x$, that is of $Z \times_{\operatorname{Spec} S} \operatorname{Spec} k$, is irreducible in Mathlib's sense (nonempty and not the union of two proper closed subsets). Second: the structure morphism $f.\mathrm{fiberToSpecResidueField}\ s$ of the scheme-theoretic fibre, namely $Z \times_{\operatorname{Spec} S} \operatorname{Spec} \kappa(s) \to \operatorname{Spec} \kappa(s)$ where $\kappa(s)$ is the residue field of $\operatorname{Spec} S$ at $s$, is geometrically irreducible. Both directions are asserted; in particular irreducibility of the base change to a single algebraically closed field with the correct kernel already suffices.
--
--   This is the standard comparison (EGA IV, 4.5.9) between the fibrewise condition 'all base changes of $f$ to algebraically closed fields lying over $s$ have irreducible total space' and geometric irreducibility of the scheme-theoretic fibre over $s$. It is used to convert the pointwise hypothesis into a statement about fibres in the openness results [`AlgebraicGeometry.isOpen_setOf_forall_irreducibleSpace_pullback_of_isProper_of_smooth`](thm.html#AlgebraicGeometry.isOpen_setOf_forall_irreducibleSpace_pullback_of_isProper_of_smooth) and its Noetherian variant, and in the analysis of geometric fibres of smooth group schemes via [`GoodReductionJacobian.RelativeGroupLaw.smooth_irreducibleSpace_geometricFibre_iff_of_ker_eq_ker`](thm.html#GoodReductionJacobian.RelativeGroupLaw.smooth_irreducibleSpace_geometricFibre_iff_of_ker_eq_ker).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_forall_irreducibleSpace_pullback_iff_geometricallyIrreducible_fiberToSpecResidueField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.forall_irreducibleSpace_pullback_iff_geometricallyIrreducible_fiberToSpecResidueField
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S)) (s : ↥(Spec (CommRingCat.of S))) :
    (∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
        RingHom.ker x = s.asIdeal → IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x)))) ↔
      GeometricallyIrreducible (f.fiberToSpecResidueField s) := by sorry
