-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_isIsogenyOfHeight_four_mul_of_isAlgClosed
-- name    : CerednikDrinfeld.SpecialFormalODModule.exists_isIsogenyOfHeight_four_mul_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/b356d515-a011-59f7-bebe-39fe1d8195e7
-- title:
--   Height-4n isogenies between special formal mathcal O_D-modules
-- statement:
--   Let $p$ be a prime, let $k$ be an algebraically closed field of characteristic $p$, and let $j \colon \mathrm{W}(\mathbb F_{p^2}) \to k$ be a ring homomorphism, where [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17) is the Witt vectors of the field with $p^2$ elements. Let $\Phi$ and $\Phi'$ be two objects of [`CerednikDrinfeld.SpecialFormalODModule p j`](def/CerednikDrinfeld_SpecialFormalModule.html#L403): each consists of a commutative formal group law $F$ in two variables over $k$, an action $a \mapsto \mathrm{act}(a)$ of $\mathrm{W}(\mathbb F_{p^2})$ by pairs of power series that are endomorphisms of the law, unital, multiplicative under composition and additive via $F$, together with a further endomorphism $\varpi$ of the law satisfying $\varpi \circ \varpi = \mathrm{act}(p)$ and $\varpi \circ \mathrm{act}(a) = \mathrm{act}(\sigma a) \circ \varpi$ for the Witt vector Frobenius $\sigma$; it is required in addition that the two Lie summands attached to $j$ be complementary and each an invertible $k$-module, and that $\mathrm{act}(p)$ have kernel algebra of degree $p^4$. The assertion is that there exist a pair of power series $\rho \in (k[[X_1,X_2]])^2$ and a natural number $n$ such that $\rho$ is an isogeny of height $4n$ from $\Phi$ to $\Phi'$: $\rho$ is a homomorphism of formal group laws $F_\Phi \to F_{\Phi'}$ commuting with $\mathrm{act}(a)$ for every $a$ and with $\varpi$, and its kernel algebra $k[[X_1,X_2]]/(\rho_1,\rho_2)$ is a finite projective $k$-module whose base change along any ring homomorphism from $k$ to a field $\kappa$ has $\kappa$-dimension $p^{4n}$.
--
--   This is the local isogeny statement underlying the Čerednik–Drinfeld uniformisation, in the normalised form that Drinfeld's moduli problem uses: an isogeny of height $4n$ is the same as an $\mathcal O_D$-linear quasi-isogeny of height zero, obtained as $p^{-n}\rho$. It refines the bare existence of an isogeny between any two special formal $\mathcal O_D$-modules of height $4$ over an algebraically closed field of characteristic $p$ by pinning the height down to a multiple of $4$, and is used in the construction of rigidified special formal $\mathcal O_D$-modules and of the quotient bridge for quaternionic formal modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_exists_isIsogenyOfHeight_four_mul_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.SpecialFormalODModule.exists_isIsogenyOfHeight_four_mul_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (j : CerednikDrinfeld.Zp2 p →+* k) (Φ Φ' : CerednikDrinfeld.SpecialFormalODModule p j) :
    ∃ (ρ : CerednikDrinfeld.SpecialFormal.Series k) (n : ℕ),
      CerednikDrinfeld.FormalODModule.IsIsogenyOfHeight Φ.toFormalODModule Φ'.toFormalODModule
        ρ (4 * n) := by sorry
