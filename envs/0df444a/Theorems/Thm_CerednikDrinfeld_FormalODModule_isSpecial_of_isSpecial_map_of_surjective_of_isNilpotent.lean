-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecial_of_isSpecial_map_of_surjective_of_isNilpotent
-- name    : CerednikDrinfeld.FormalODModule.isSpecial_of_isSpecial_map_of_surjective_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/3519bf30-e82a-5f9e-944b-a1f29cdba81a
-- title:
--   Speciality descends along surjections with nilpotent kernel
-- statement:
--   Let $p$ be a prime, let $R$ and $S$ be commutative rings, and let $\pi \colon R \to S$ be a surjective ring homomorphism whose kernel is a nilpotent ideal (some power of $\ker \pi$ vanishes); assume moreover that the image of $p$ in $R$ is nilpotent. Let $j \colon \mathbb{Z}_{p^2} \to R$ be a ring homomorphism, where $\mathbb{Z}_{p^2}$ denotes `Zp2 p`, the Witt vectors of the field with $p^2$ elements, and let $X$ be a formal $\mathcal{O}_D$-module over $R$: a commutative two-dimensional formal group law $X.F$ together with series $X.\mathrm{act}\,a$ ($a \in \mathbb{Z}_{p^2}$) and $X.\varpi$, each a pair of power series in two variables that is an endomorphism of $X.F$, subject to $X.\mathrm{act}\,1 = \mathrm{id}$, multiplicativity and additivity of $a \mapsto X.\mathrm{act}\,a$ (composition, resp. addition via $X.F$), $X.\varpi \circ X.\varpi = X.\mathrm{act}\,p$ and $X.\varpi \circ X.\mathrm{act}\,a = X.\mathrm{act}(\sigma a) \circ X.\varpi$ for the Witt vector Frobenius $\sigma$. Write $X.\mathrm{map}\,\pi$ for the coefficientwise base change of $X$ along $\pi$. Speciality of a formal $\mathcal{O}_D$-module $Y$ over a ring $B$ relative to $j' \colon \mathbb{Z}_{p^2} \to B$ asserts that the two submodules $\bigwedge_a \ker(Y.\mathrm{lieAct}\,a - j'(a))$ and $\bigwedge_a \ker(Y.\mathrm{lieAct}\,a - j'(\sigma a))$ of $Y.\mathrm{Lie}$, intersections over all $a \in \mathbb{Z}_{p^2}$, are complementary and each invertible as a $B$-module. The theorem states: if $X.\mathrm{map}\,\pi$ is special over $S$ relative to $\pi \circ j$, then $X$ is special over $R$ relative to $j$.
--
--   This is the descent of the speciality condition on a formal $\mathcal{O}_D$-module along a nilpotent thickening of the base, in the sense of the Čerednik–Drinfeld theory of special formal modules. It is used in the construction of admissible rigidified objects, where speciality over a truncated base has to be propagated to the ambient ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_isSpecial_of_isSpecial_map_of_surjective_of_isNilpotent.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.isSpecial_of_isSpecial_map_of_surjective_of_isNilpotent
    (p : ℕ) [Fact p.Prime] {R S : Type} [CommRing R] [CommRing S]
    (π : R →+* S) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π)) (hp : IsNilpotent (p : R))
    (j : Zp2 p →+* R) (X : FormalODModule p R) (h : (X.map π).IsSpecial (π.comp j)) :
    X.IsSpecial j := by sorry
