-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_IsSpecial_of_isODHom_of_comp_eq_id
-- name    : CerednikDrinfeld.FormalODModule.IsSpecial.of_isODHom_of_comp_eq_id
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/5348b9f8-0077-5650-b9a4-1c10e839a6c3
-- title:
--   Speciality transports along isomorphisms of formal 𝒪_D-modules
-- statement:
--   Fix a prime $p$, a commutative ring $B$ and a ring homomorphism $j \colon \mathbb{Z}_{p^2} \to B$, where $\mathbb{Z}_{p^2}$ is realised as the Witt vectors of the field with $p^2$ elements. Let $Y$ and $Y'$ be formal $\mathcal{O}_D$-modules over $B$ in the sense of `FormalODModule`: each consists of a commutative $2$-dimensional formal group law over $B$, an action $a \mapsto \mathrm{act}(a)$ of $\mathbb{Z}_{p^2}$ by endomorphisms of that law given by pairs of power series in two variables, and a further endomorphism $\varpi$, subject to the usual relations ($\mathrm{act}$ multiplicative and additive, $\varpi \circ \varpi = \mathrm{act}(p)$, and $\varpi \circ \mathrm{act}(a) = \mathrm{act}(\sigma a) \circ \varpi$ for the Witt Frobenius $\sigma$). Let $u, v$ be pairs of power series in two variables over $B$ such that $u$ is a homomorphism $Y \to Y'$ and $v$ a homomorphism $Y' \to Y$ of formal $\mathcal{O}_D$-modules (each a homomorphism of formal group laws commuting with all $\mathrm{act}(a)$ and with $\varpi$), and assume the two substitution identities $v \circ u = \mathrm{id}$ and $u \circ v = \mathrm{id}$. If $Y$ is special for $j$, i.e. the submodules $\mathrm{lieZero}_j(Y) = \bigcap_a \ker(\mathrm{lieAct}(a) - j(a))$ and $\mathrm{lieOne}_j(Y) = \bigcap_a \ker(\mathrm{lieAct}(a) - j(\sigma a))$ of $Y.\mathrm{Lie}$ are complementary and both invertible $B$-modules, then $Y'$ is special for $j$ in the same sense.
--
--   This is the invariance of the speciality condition on formal $\mathcal{O}_D$-modules under isomorphism, as used in the Čerednik–Drinfel'd uniformisation of Shimura curves. It is invoked when speciality must be propagated along an identification of formal modules, in the rigidification statement for fake elliptic curves and in the construction of the moduli scheme attached to the special formal module problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_IsSpecial_of_isODHom_of_comp_eq_id.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.IsSpecial.of_isODHom_of_comp_eq_id
    {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] (j : Zp2 p →+* B)
    (Y Y' : FormalODModule p B) (u v : Series B)
    (hu : FormalODModule.IsODHom Y Y' u) (hv : FormalODModule.IsODHom Y' Y v)
    (hvu : v.comp u = Series.id B) (huv : u.comp v = Series.id B)
    (hY : Y.IsSpecial j) : Y'.IsSpecial j := by sorry
