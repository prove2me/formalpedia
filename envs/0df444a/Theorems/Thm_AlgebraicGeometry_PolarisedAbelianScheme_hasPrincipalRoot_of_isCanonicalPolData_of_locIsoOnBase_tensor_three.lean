-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_hasPrincipalRoot_of_isCanonicalPolData_of_locIsoOnBase_tensor_three
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.hasPrincipalRoot_of_isCanonicalPolData_of_locIsoOnBase_tensor_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/1e0cdb54-8986-5f2e-95cf-53271a6cc5dd
-- title:
--   Cube root of a polarisation yields a principal root
-- statement:
--   Let $g,d,n$ be natural numbers, $S$ a commutative ring and $u$ a polarised abelian scheme of type $(g,d,n)$ over $S$: a scheme $u.A$ with structure morphism $u.f : u.A \to \operatorname{Spec} S$, a commutative relative group law $u.L$, the smooth–proper–connected-fibres bundle, fibres of topological Krull dimension $g$, a family of $2g$ sections killed by $n$ which freely generate the $n$-torsion of every geometric fibre, and an invertible module $u.pol$ whose sections give a closed immersion into a projective space and whose geometric fibre $H^0$ has rank $d$ everywhere. Let $I$ be a type, $act : I \to \operatorname{End}(u.A)$ a family of endomorphisms over $\operatorname{Spec} S$, $star : I \to I$ an involution-datum, and $polE$ a module on $u.A$ satisfying [`CerednikDrinfeld.QM.IsCanonicalPolData`](def/CerednikDrinfeld_QMCanonicalPol.html#L15): $polE$ is invertible, symmetric and with two-torsion kernel in the `LocIsoOnBase` sense, has everywhere positive geometric fibre $H^0$-rank, is Rosati-compatible with $act$ and $star$, and admits, after a faithfully flat $S \to S'$ and for every compatible group law $L'$ on the base change, an invertible $\mathcal L_0$ with trivial kernel such that $polE$ pulled back is locally isomorphic on the base to $\mathcal L_0 \otimes [-1]^*\mathcal L_0$. Assume moreover that $u.pol$ and $polE \otimes polE \otimes polE$ are isomorphic after pullback to $u.f^{-1}(U)$ for suitable open $U$ around each point of $\operatorname{Spec} S$. Then `PolarisedAbelianScheme.HasPrincipalRoot u` holds: there is a faithfully flat $S$-algebra $S'$ such that for every relative group law $L'$ on the base change of $u.f$ compatible with $u.L$ there exist an invertible module $\mathcal L_0$ with trivial kernel and natural numbers $a,b$ with $1 \le a+b$ for which the pullback of $u.pol$ is locally isomorphic on the base to $\mathcal L_0^{\otimes a} \otimes ([-1]^*\mathcal L_0)^{\otimes b}$ in the sense of `Scheme.Modules.tpow`.
--
--   This is the step that converts a canonical quaternionic polarisation datum whose cube computes the given polarisation into the existence of a principal root of that polarisation after a faithfully flat base change. It feeds the construction of rooted symmetric data of type $(6,6)$ for quaternionic multiplication structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_hasPrincipalRoot_of_isCanonicalPolData_of_locIsoOnBase_tensor_three.lean

import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.PolarisedAbelianScheme.hasPrincipalRoot_of_isCanonicalPolData_of_locIsoOnBase_tensor_three
    {g d n : ℕ} {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    {I : Type} (act : I → (u.A ⟶ u.A)) (act_over : ∀ x : I, act x ≫ u.f = u.f) (star : I → I)
    (polE : u.A.Modules) (hE : CerednikDrinfeld.QM.IsCanonicalPolData u.f u.L act act_over star polE)
    (hloc : LocIsoOnBase u.f u.pol (polE ⊗ polE ⊗ polE)) :
    PolarisedAbelianScheme.HasPrincipalRoot u := by sorry
