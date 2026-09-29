-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_eq_comp_of_memKernel_of_isOfType_of_isAlgClosed
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_eq_comp_of_memKernel_of_isOfType_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/9bb2c817-3693-5283-9e5d-c3e07868ea86
-- title:
--   Kernel points over an algebraically closed base point do not grow
-- statement:
--   Fix natural numbers $g,d,n$, a function $\delta : \mathrm{Fin}\,g \to \mathbb N$, a commutative ring $S$ and a polarised abelian scheme $u$ of invariants $(g,d,n)$ over $S$, with structure morphism $u.f : u.A \to \operatorname{Spec} S$, relative group law $u.L$ and polarising module $u.\mathrm{pol}$. Assume `PolarisedAbelianScheme.IsOfType δ u`: there are a faithfully flat étale $S$-algebra $S'$ and a family $x' : (\prod_i \mathbb Z/\delta_i) \times (\prod_i \mathbb Z/\delta_i) \to$ sections of $u.f$ over $\operatorname{Spec} S'$ which is additive for $u.L$, is injective on geometric points over algebraically closed fields, and is such that for every $S'$-algebra $R$ an $R$-point $y$ of $u.A$ lies in the kernel `Polarisation.MemKernel u.f u.L u.pol` (the pullback of the Mumford bundle of $u.\mathrm{pol}$ along the slice at $y$ is, locally on the base, isomorphic to the unit module) if and only if, after passing to the members of a cover of $\operatorname{Spec} R$ by basic opens, $y$ agrees with some $x'_h$. Let $K$ be an algebraically closed field, $t : \operatorname{Spec} K \to \operatorname{Spec} S$, and $x$ a family of morphisms $\operatorname{Spec} K \to u.A$ over $t$, indexed by the same group $(\prod_i \mathbb Z/\delta_i)^2$, such that every $K$-point over $t$ in the kernel equals some $x_h$ (no homomorphism or injectivity property of $x$ is assumed). Let $L$ be a field, $\psi : K \to L$ a ring homomorphism, and $y$ a morphism $\operatorname{Spec} L \to u.A$ over $\operatorname{Spec}\psi$ followed by $t$ which lies in the kernel. Then there is an index $h$ with $y = \operatorname{Spec}\psi$ followed by $x_h$, as morphisms of schemes.
--
--   This is the statement that over an algebraically closed base point the kernel $K(\mathcal L)$ of the polarisation acquires no further points in any field extension, a finiteness/constancy property of the kernel for a polarisation of type $\delta$. It is used in the construction of principal roots and theta points for rooted symmetric polarisations of given type, in [`AlgebraicGeometry.PolarisedAbelianScheme.exists_isAlgClosed_principalRoot_thetaPt_of_rootedSymmetricOfType`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_isAlgClosed_principalRoot_thetaPt_of_rootedSymmetricOfType).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_eq_comp_of_memKernel_of_isOfType_of_isAlgClosed.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators MonoidalCategory

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_eq_comp_of_memKernel_of_isOfType_of_isAlgClosed
    {g d n : ℕ} (δ : Fin g → ℕ) {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    (hu : PolarisedAbelianScheme.IsOfType δ u)
    {K : Type} [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of S))
    (x : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → SchemeHomOver t u.f)
    (hxK : ∀ y : SchemeHomOver t u.f, Polarisation.MemKernel u.f u.L u.pol t y →
      ∃ h : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))), y = x h)
    {L : Type} [Field L] (ψ : K →+* L)
    (y : SchemeHomOver (Spec.map (CommRingCat.ofHom ψ) ≫ t) u.f)
    (hy : Polarisation.MemKernel u.f u.L u.pol (Spec.map (CommRingCat.ofHom ψ) ≫ t) y) :
    ∃ h : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))), y.1 = Spec.map (CommRingCat.ofHom ψ) ≫ (x h).1 := by sorry
