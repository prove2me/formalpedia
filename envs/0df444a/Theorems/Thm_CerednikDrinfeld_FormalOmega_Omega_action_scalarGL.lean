-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_Omega_action_scalarGL
-- name    : CerednikDrinfeld.FormalOmega.Omega.action_scalarGL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/5825e83c-cb94-542e-9144-ee4ab552d214
-- title:
--   Homotheties act trivially on Drinfeld's formal upper half plane
-- statement:
--   Let $\mathcal O$ be a commutative ring, $K$ a field equipped with an $\mathcal O$-algebra structure, $\pi$ an element of $\mathcal O$, and $B$ a commutative $\mathcal O$-algebra. Let $c \in K^\times$ and let $d$ be a $B$-point of the functor `Omega K π`, that is, a Deligne datum over $B$: an assignment, to every full $\mathcal O$-lattice $M \subseteq K^2$, of a $B$-submodule $d.\mathrm{line}\,M$ of the base change $B \otimes_{\mathcal O} M$ whose quotient is an invertible $B$-module, compatible with lattice inclusions (the image of $d.\mathrm{line}\,M'$ under $B \otimes M' \to B \otimes M$ lies in $d.\mathrm{line}\,M$ when $M' \le M$), satisfying the homothety law $d.\mathrm{line}(cM) =$ the image of $d.\mathrm{line}\,M$ under the isomorphism induced by $v \mapsto cv$, and satisfying the stated nondegeneracy condition at every prime ideal of $B$. The assertion is that the scalar matrix $\mathrm{scalarGL}\,c = c \cdot 1 \in \mathrm{GL}_2(K)$ acts on $d$ as the identity, where the $\mathrm{GL}_2(K)$-action `Omega.action K π` sends $g$ and $d$ to the pullback datum whose line at $M$ is the preimage of $d.\mathrm{line}(g^{-1}M)$ under the base change of $v \mapsto g^{-1}v$; thus $(\mathrm{scalarGL}\,c) \cdot d = d$.
--
--   This records that the $\mathrm{GL}_2(K)$-action on Drinfeld's formal upper half plane factors through $\mathrm{PGL}_2(K)$, the scalars acting trivially on Deligne data. It is used throughout the Čerednik–Drinfeld part of the development, where the group acting on $\widehat\Omega$ enters through a representation into $\mathrm{PGL}_2$ of the local field, for instance in the analysis of adic points and of the Mumford tower.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_Omega_action_scalarGL.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.Omega.action_scalarGL
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    (B : Type) [CommRing B] [Algebra 𝒪 B] (c : Kˣ) (d : (Omega K π).obj B) :
    (Omega.action K π).act B (scalarGL c) d = d := by sorry
