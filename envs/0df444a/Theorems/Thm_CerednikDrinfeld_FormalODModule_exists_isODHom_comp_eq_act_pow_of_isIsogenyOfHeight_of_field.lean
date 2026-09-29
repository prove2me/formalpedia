-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isODHom_comp_eq_act_pow_of_isIsogenyOfHeight_of_field
-- name    : CerednikDrinfeld.FormalODModule.exists_isODHom_comp_eq_act_pow_of_isIsogenyOfHeight_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/06e03a29-7c32-5f15-8069-05216ff8d111
-- title:
--   A power of p factors through an isogeny of formal 𝒪_D-modules
-- statement:
--   Let $p$ be a prime and let $B$ be a field in which $p$ is nilpotent, i.e. of characteristic $p$. Let $X$ and $Y$ be formal $\mathcal{O}_D$-modules over $B$ in the sense of `FormalODModule`: each consists of a commutative two-dimensional formal group law over $B$, an action `act` of the ring $\mathbb{Z}_{p^2}$ of Witt vectors of $\mathbb{F}_{p^2}$ by endomorphisms of that law (multiplicative for composition, additive for addition along the law, with $\mathrm{act}(1)$ the identity), and a further endomorphism `varpi` satisfying $\varpi\circ\varpi=\mathrm{act}(p)$ and $\varpi\circ\mathrm{act}(a)=\mathrm{act}(\sigma a)\circ\varpi$ for the Witt vector Frobenius $\sigma$. Let $\rho$ be a pair of power series in two variables and $h$ a natural number such that $\rho$ is an isogeny of height $h$ from $X$ to $Y$, that is: $\rho$ is a homomorphism of the underlying laws commuting with the $\mathbb{Z}_{p^2}$-action and with $\varpi$, and the associated kernel algebra `KerAlgebra` of $\rho$ is finite and projective over $B$ with fibre dimension $p^h$ over every field receiving $B$. The conclusion asserts that there are a natural number $N$ and a pair of power series $\beta$ which is a homomorphism of formal $\mathcal{O}_D$-modules from $Y$ to $X$ with $\beta\circ\rho=\mathrm{act}_X(p^N)$.
--
--   This is the statement that an isogeny of formal $\mathcal{O}_D$-modules in characteristic $p$ admits a quasi-inverse: multiplication by a suitable power of $p$ on the source factors through it. It is used in the Čerednik–Drinfeld part of the development, both in the version over a maximal base and in the study of isogenies and Atkin–Lehner data on fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_isODHom_comp_eq_act_pow_of_isIsogenyOfHeight_of_field.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.exists_isODHom_comp_eq_act_pow_of_isIsogenyOfHeight_of_field
    (p : ℕ) [Fact p.Prime] {B : Type} [Field B] (hB : IsNilpotent (p : B))
    (X Y : FormalODModule p B) (ρ : Series B) (h : ℕ) (hρ : FormalODModule.IsIsogenyOfHeight X Y ρ h) :
    ∃ (N : ℕ) (β : Series B), FormalODModule.IsODHom Y X β ∧ β.comp ρ = X.act ((p : Zp2 p) ^ N) := by sorry
