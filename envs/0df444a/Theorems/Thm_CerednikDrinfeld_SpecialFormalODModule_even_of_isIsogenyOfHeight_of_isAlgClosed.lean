-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_even_of_isIsogenyOfHeight_of_isAlgClosed
-- name    : CerednikDrinfeld.SpecialFormalODModule.even_of_isIsogenyOfHeight_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/0f972f66-a264-5c66-ad72-d67fdb84190b
-- title:
--   Isogenies of special formal mathcal O_D-modules have even height
-- statement:
--   Let $p$ be a prime and $k$ an algebraically closed field of characteristic $p$, equipped with a ring homomorphism $j$ from $\mathbb Z_{p^2} = W(\mathbb F_{p^2})$ (the Witt vectors of `GaloisField p 2`) to $k$. Let $\Phi$ and $\Phi'$ be special formal $\mathcal O_D$-modules over $k$ relative to $j$: each consists of a two-dimensional commutative formal group law $F$ over $k$, a family of law endomorphisms $\mathrm{act}(a)$ for $a \in \mathbb Z_{p^2}$ which is unital, multiplicative for composition and additive for the group law, together with a law endomorphism $\varpi$ satisfying $\varpi \circ \varpi = \mathrm{act}(p)$ and $\varpi \circ \mathrm{act}(a) = \mathrm{act}(\sigma a) \circ \varpi$ for the Witt vector Frobenius $\sigma$; specialness, meaning that the two Lie eigenspaces `lieZero j` and `lieOne j` are complementary and each invertible as a $k$-module; and height $4$, meaning that $\mathrm{act}(p)$ has kernel of degree $p^4$. Let $\rho$ be a pair of power series in two variables over $k$ and $h$ a natural number, and assume $\rho$ is an isogeny of height $h$ from $\Phi$ to $\Phi'$: $\rho$ is a homomorphism of formal group laws commuting with every $\mathrm{act}(a)$ and with $\varpi$, its kernel algebra is finite and projective over $k$, and has dimension $p^h$ over every field-valued point. Then $h$ is even.
--
--   This is the parity assertion contained in the Boutot–Carayol analysis of isogenies between special formal $\mathcal O_D$-modules, proved through the graded covariant Cartier module, where the two graded pieces of the cokernel have equal length. It is used in the constructions of isogenies of prescribed even height that enter the Čerednik–Drinfel'd description of $p$-adic uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_even_of_isIsogenyOfHeight_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.SpecialFormalODModule.even_of_isIsogenyOfHeight_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (j : CerednikDrinfeld.Zp2 p →+* k) (Φ Φ' : CerednikDrinfeld.SpecialFormalODModule p j)
    (ρ : CerednikDrinfeld.SpecialFormal.Series k) (h : ℕ)
    (hρ : CerednikDrinfeld.FormalODModule.IsIsogenyOfHeight Φ.toFormalODModule Φ'.toFormalODModule ρ h) :
    Even h := by sorry
