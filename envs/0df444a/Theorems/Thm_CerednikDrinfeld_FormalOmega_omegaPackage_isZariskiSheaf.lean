-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_omegaPackage_isZariskiSheaf
-- name    : CerednikDrinfeld.FormalOmega.omegaPackage_isZariskiSheaf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/360dedb4-a078-5b27-9a94-3e90c4d94507
-- title:
--   Zariski descent for the formal upper half-plane moduli package
-- statement:
--   Let $\mathcal{O}$ be a commutative ring, $K$ a field equipped with an $\mathcal{O}$-algebra structure, $O$ a commutative ring, $p$ a prime, $\pi \in \mathcal{O}$, and $c \colon \mathcal{O} \to O$ a ring homomorphism. Consider the moduli package `omegaPackage p π c`, obtained from the functor `Omega K π` on $\mathcal{O}$-algebras — whose value at an $\mathcal{O}$-algebra $B$ is the type `DeligneDatum π B` and whose transition maps are `DeligneDatum.map` — by reading a ring homomorphism $\psi \colon O \to B$ as the $\mathcal{O}$-algebra structure $\psi \circ c$ on $B$ (so the value ignores the accompanying nilpotence datum). The assertion is that this package satisfies `IsZariskiSheaf`: for every commutative ring $B$, every ring map $\psi \colon O \to B$, every witness that $p$ is nilpotent in $B$, every $n$ and every family $f \colon \mathrm{Fin}\,n \to B$ with $\mathrm{span}(\mathrm{range}\,f) = \top$, every choice of $B$-algebras $L_i$ that are localisations away from $f_i$ and $L_{ij}$ that are localisations away from $f_i f_j$, in which $p$ is nilpotent, and every pair of families of ring maps $l_{ij} \colon L_i \to L_{ij}$, $r_{ij} \colon L_j \to L_{ij}$ compatible with the structural maps from $B$: (i) two Deligne data over $B$ whose base changes to each $L_i$ agree are equal; and (ii) a family of Deligne data over the $L_i$ whose images in each $L_{ij}$ along $l_{ij}$ and $r_{ij}$ agree is the base change of a Deligne datum over $B$.
--
--   This is the Zariski sheaf (descent) axiom for the moduli package attached to Drinfeld's formal upper half-plane, in the form required by the package formalism for special formal $\mathcal{O}_D$-modules; it is used in the proof that the associated period map is bijective over Noetherian rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_omegaPackage_isZariskiSheaf.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_OmegaModuliPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalOmega.omegaPackage_isZariskiSheaf
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {O : Type} [CommRing O]
    (p : ℕ) [Fact p.Prime] (π : 𝒪) (c : 𝒪 →+* O) :
    (omegaPackage (K := K) p π c).IsZariskiSheaf := by sorry
