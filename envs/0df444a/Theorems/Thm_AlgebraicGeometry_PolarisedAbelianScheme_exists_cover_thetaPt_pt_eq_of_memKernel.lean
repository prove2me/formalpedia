-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_cover_thetaPt_pt_eq_of_memKernel
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_cover_thetaPt_pt_eq_of_memKernel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/206516ab-541f-5365-a60b-853d447204a2
-- title:
--   Theta points over a kernel point, Zariski-locally on the base
-- statement:
--   Fix naturals $g,d,n$, a commutative ring $S$ and a polarised abelian scheme $u$ of type $(g,d,n)$ over $S$: this is a structure consisting of a scheme $u.A$ with a morphism $u.f : u.A \to \operatorname{Spec} S$, a commutative relative group law $u.L$, the property bundle of an abelian scheme, fibres of topological Krull dimension $g$, a family of $2g$ $n$-torsion sections generating $(\mathbb Z/n)^{2g}$ freely on geometric fibres, and an invertible $u.A$-module $u.pol$ which is a closed immersion by its sections over $\operatorname{Spec} S$ and has geometric fibre $H^0$-rank $d$. Let $R$ be a commutative ring, $t : \operatorname{Spec} R \to \operatorname{Spec} S$ a morphism, and $y$ a morphism $\operatorname{Spec} R \to u.A$ over $t$. Assume `Polarisation.MemKernel u.f u.L u.pol t y`: for every point of $\operatorname{Spec} R$ there is an open neighbourhood $U$ such that, on the preimage of $U$ under the second projection $u.A \times_S \operatorname{Spec} R \to \operatorname{Spec} R$, the pullback along the slice $(\mathrm{pr}_1, y \circ \mathrm{pr}_2)$ of the Mumford bundle $m^*u.pol \otimes \mathrm{pr}_1^* u.pol^\vee \otimes \mathrm{pr}_2^* u.pol^\vee$ is isomorphic to the unit module. The conclusion: there are $m \in \mathbb N$ and $r : \mathrm{Fin}\, m \to R$ whose range spans the unit ideal such that for each $j$ there is a `ThetaPt` of $u.pol$ over the composite $\operatorname{Spec} R[1/r_j] \to \operatorname{Spec} R \to \operatorname{Spec} S$ — that is, a point of $u.A$ over that base together with an isomorphism between the pullback of $u.pol$ to $u.A \times_S \operatorname{Spec} R[1/r_j]$ and its translate by that point — whose underlying point is the base change of $y$ along $R \to R[1/r_j]$.
--
--   This is the local existence of a theta-group lift of a point of the kernel $K(\mathcal L)$ of the polarisation: a point killed by the Mumford bundle condition acquires, after inverting a suitable element of the base, an isomorphism $\tau_y^*\mathcal L \cong \mathcal L$, i.e. a point of the theta group lying over it. It is used in the construction of level lifts for polarised abelian schemes of a given type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_cover_thetaPt_pt_eq_of_memKernel.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_cover_thetaPt_pt_eq_of_memKernel
    {g d n : ℕ} {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (y : SchemeHomOver t u.f) (hy : Polarisation.MemKernel u.f u.L u.pol t y) :
    ∃ (m : ℕ) (r : Fin m → R), Ideal.span (Set.range r) = ⊤ ∧
      ∀ j : Fin m, ∃ θ : ThetaPt u.f u.L u.pol
          (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (r j)))) ≫ t),
        (θ.pt).1 = Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (r j)))) ≫ y.1 := by sorry
