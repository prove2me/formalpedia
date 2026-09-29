-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_IsSpecial_map
-- name    : CerednikDrinfeld.FormalODModule.IsSpecial.map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/7a453a5b-7340-5325-99d0-395d322d8c6e
-- title:
--   Speciality of a formal mathcal O_D-module is stable under base change
-- statement:
--   Let $p$ be a prime, let $B$ and $B'$ be commutative rings, let $j \colon \mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2}) \to B$ and $f \colon B \to B'$ be ring homomorphisms, where $\mathbb{Z}_{p^2}$ denotes `Zp2 p`, the Witt vectors of `GaloisField p 2`, and let $X$ be a term of `FormalODModule p B`: a commutative $2$-dimensional multivariate formal group law $F$ over $B$ together with systems of power series `act a` (for $a \in \mathbb{Z}_{p^2}$) and `varpi`, each an endomorphism of $F$ in the sense of `IsLawHom`, with `act` multiplicative, additive via $F$ and unital, $\mathrm{varpi} \circ \mathrm{varpi} = \mathrm{act}(p)$ and $\mathrm{varpi} \circ \mathrm{act}(a) = \mathrm{act}(\sigma a) \circ \mathrm{varpi}$ for the Witt vector Frobenius $\sigma$. Assume `X.IsSpecial j`, that is: inside the $B$-module `X.Lie`, the submodule `X.lieZero j` $= \bigcap_a \ker(\mathrm{lieAct}(a) - j(a))$ and the submodule `X.lieOne j` $= \bigcap_a \ker(\mathrm{lieAct}(a) - j(\sigma a))$ are complementary, and both are invertible $B$-modules. Then the base change `X.map f`, obtained by applying `MvPowerSeries.map f` to $F$, to every `act a` and to `varpi`, satisfies `IsSpecial (f.comp j)`: the corresponding two submodules of its Lie module, cut out by the eigenvalues $f(j(a))$ and $f(j(\sigma a))$, are complementary and invertible over $B'$.
--
--   This is the base-change stability of the Drinfeld speciality condition on formal $\mathcal O_D$-modules of dimension $2$, which splits the Lie module into the two eigen-lines for the action of $\mathbb{Z}_{p^2}$ and its Frobenius twist. It is used throughout the Čerednik–Drinfeld part of the development whenever a special formal $\mathcal O_D$-module is transported along a ring homomorphism, for instance in passing to an algebraically closed base or to a reduction, as in the critical-chart and Cartier-quadruple constructions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_IsSpecial_map.lean

import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.IsSpecial.map
    {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {B' : Type v} [CommRing B']
    (j : Zp2 p →+* B) (f : B →+* B') (X : FormalODModule p B) (hX : X.IsSpecial j) :
    (X.map f).IsSpecial (f.comp j) := by sorry
