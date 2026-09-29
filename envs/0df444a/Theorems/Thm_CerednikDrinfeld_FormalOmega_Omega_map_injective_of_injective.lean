-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_Omega_map_injective_of_injective
-- name    : CerednikDrinfeld.FormalOmega.Omega.map_injective_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/0d06153a-4c4d-5e14-8881-e8b67bb61610
-- title:
--   Deligne data inject along injective algebra maps
-- statement:
--   Let $\mathcal O$ be a commutative ring, $K$ a field equipped with an $\mathcal O$-algebra structure, and $\pi \in \mathcal O$. Let $S'$ and $B'$ be commutative $\mathcal O$-algebras and let $\varphi : S' \to B'$ be an $\mathcal O$-algebra homomorphism which is injective as a map of sets. The assertion is that the map on objects induced by $\varphi$ under the functor `Omega K π` on $\mathcal O$-algebras is injective. Concretely, an element of `Omega K π` at a base $B$ is a `DeligneDatum`: a family of $B$-submodules $N_M \subseteq B \otimes_{\mathcal O} M$ indexed by the full lattices $M$ in $K^2$, such that each quotient $(B \otimes_{\mathcal O} M)/N_M$ is an invertible $B$-module, such that $N_{M'}$ maps into $N_M$ under the map induced by an inclusion $M' \subseteq M$, such that $N_{cM}$ is the image of $N_M$ under the scalar matrix $c \in K^\times$, and satisfying the nondegeneracy clause at every prime $\mathfrak p$ of $B$ formulated with $\pi$. The induced map sends such a datum to the one whose line at $M$ is the $B'$-span of the image of $N_M$ under $\varphi \otimes \mathrm{id}_M$. Thus two Deligne data over $S'$ whose base-changed lines agree at every lattice coincide.
--
--   This is the injectivity on points of Drinfeld's formal upper half plane functor, in its description by lines with invertible quotient, along an injective map of $\mathcal O$-algebras; no flatness of $\varphi$ is required. It is used in the finite-presentation and directedness arguments for this functor, and in the construction of pullback families in the Čerednik–Drinfeld uniformisation of Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_Omega_map_injective_of_injective.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.Omega.map_injective_of_injective
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {S' B' : Type} [CommRing S'] [Algebra 𝒪 S'] [CommRing B'] [Algebra 𝒪 B'] (φ : S' →ₐ[𝒪] B')
    (hφ : Function.Injective φ) : Function.Injective ((Omega K π).map φ) := by sorry
