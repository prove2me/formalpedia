-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_Omega_isSeparated_of_equiv_nilpPoints
-- name    : CerednikDrinfeld.FormalOmega.Omega.isSeparated_of_equiv_nilpPoints
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/c76a4794-fc39-5322-852b-bb1b726b181d
-- title:
--   Separatedness of a scheme representing the Deligne datum functor
-- statement:
--   Let $p$ be a prime, let $C$ be a commutative ring equipped with a $\mathbb{Z}_p$-algebra structure, let $X$ be a scheme and let $f \colon X \to \operatorname{Spec} C$ be a morphism. Write $\Omega$ for the functor on commutative $\mathbb{Z}_p$-algebras that sends $S$ to the set of Deligne data over $S$ relative to $K = \mathbb{Q}_p$ and the element $p \in \mathbb{Z}_p$: families assigning to every full $\mathbb{Z}_p$-lattice $M \subset \mathbb{Q}_p^2$ a submodule $\mathrm{line}(M) \subseteq S \otimes_{\mathbb{Z}_p} M$ whose quotient is an invertible $S$-module, compatible with lattice inclusions, equivariant for homotheties by $c \in \mathbb{Q}_p^\times$, and satisfying the nondegeneracy condition at every prime ideal of $S$; on an algebra map it acts by spanning the image of the line under base change. Assume given, for every commutative ring $S$ that is simultaneously a $C$-algebra and a $\mathbb{Z}_p$-algebra compatibly, a bijection $\mathrm{pt}_S$ from $\Omega(S)$ onto the set of morphisms $\varphi \colon \operatorname{Spec} S \to X$ with $\varphi$ followed by $f$ equal to the structure morphism $\operatorname{Spec} S \to \operatorname{Spec} C$, and assume these bijections are natural: for every $C$-algebra map $\psi \colon S \to S'$ and every $d \in \Omega(S)$, $\mathrm{pt}_{S'}$ of the base change of $d$ along $\psi$ (viewed as a $\mathbb{Z}_p$-algebra map) equals $\operatorname{Spec}(\psi)$ followed by $\mathrm{pt}_S(d)$. Then $f$ is separated.
--
--   The functor $\Omega$ is Drinfeld's formal upper half-plane described by Deligne data, and the statement says that any scheme representing it on all $C$-algebras is separated over $C$; the underlying mechanism is that the coincidence of two Deligne data is cut out by an ideal, as recorded in [`CerednikDrinfeld.FormalOmega.DeligneDatum.exists_ideal_forall_map_eq_iff_le_ker`](thm.html#CerednikDrinfeld.FormalOmega.DeligneDatum.exists_ideal_forall_map_eq_iff_le_ker). It supplies the separatedness clause in the existence theorem [`CerednikDrinfeld.FormalOmega.exists_scheme_locallyOfFiniteType_isSeparated_isReduced_equiv_omegaObj_of_isNoetherianRing`](thm.html#CerednikDrinfeld.FormalOmega.exists_scheme_locallyOfFiniteType_isSeparated_isReduced_equiv_omegaObj_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_Omega_isSeparated_of_equiv_nilpPoints.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic TensorProduct

open CategoryTheory AlgebraicGeometry

theorem CerednikDrinfeld.FormalOmega.Omega.isSeparated_of_equiv_nilpPoints
    (p : ℕ) [Fact p.Prime]
    (C : Type) [CommRing C] [Algebra ℤ_[p] C]
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of C))
    (pt : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] C S],
      (Omega ℚ_[p] (p : ℤ_[p])).obj S ≃ (Scheme.nilpPoints f).obj S)
    (hpt : ∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] C S]
        [CommRing S'] [Algebra C S'] [Algebra ℤ_[p] S'] [IsScalarTower ℤ_[p] C S']
        (φ : S →ₐ[C] S') (d : (Omega ℚ_[p] (p : ℤ_[p])).obj S),
        pt S' ((Omega ℚ_[p] (p : ℤ_[p])).map (φ.restrictScalars ℤ_[p]) d) = (Scheme.nilpPoints f).map φ (pt S d)) :
    IsSeparated f := by sorry
