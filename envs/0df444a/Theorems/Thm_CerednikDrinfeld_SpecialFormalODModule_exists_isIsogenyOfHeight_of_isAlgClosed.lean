-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_isIsogenyOfHeight_of_isAlgClosed
-- name    : CerednikDrinfeld.SpecialFormalODModule.exists_isIsogenyOfHeight_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/bda867d7-68ef-55c4-be40-b7ed46f2d887
-- title:
--   Special formal mathcal O_D-modules over algebraically closed k are isogenous
-- statement:
--   Let $p$ be a prime, let $k$ be an algebraically closed field of characteristic $p$, and let $j \colon \mathbb{Z}_{p^2} \to k$ be a ring homomorphism, where $\mathbb{Z}_{p^2}$ denotes [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17), the Witt vectors $W(\mathbb{F}_{p^2})$. Let $\Phi$ and $\Phi'$ be two objects of `SpecialFormalODModule p j`: each consists of a commutative two-dimensional formal group law $F$ over $k$ (a pair of power series in $\mathrm{Fin}\,2 \oplus \mathrm{Fin}\,2$ variables satisfying the usual normalisations, associativity and commutativity), together with a family `act` of pairs of power series indexed by $\mathbb{Z}_{p^2}$ and a further pair `varpi`, all of them endomorphisms of the law $F$, with `act 1` the identity, `act` multiplicative and additive for composition and for addition via $F$, $\mathrm{varpi} \circ \mathrm{varpi} = \mathrm{act}(p)$ and $\mathrm{varpi} \circ \mathrm{act}(a) = \mathrm{act}(\sigma a) \circ \mathrm{varpi}$ for the Witt vector Frobenius $\sigma$; which is special for $j$, in the sense that the two pieces `lieZero j` and `lieOne j` of the tangent space are complementary and each invertible as a $k$-module; and which has height $4$, in the sense that the kernel algebra of $\mathrm{act}(p)$ is finite and projective over $k$ and has rank $p^4$ over every field receiving a ring homomorphism from $k$. The conclusion is that there exist a pair $\rho$ of power series in two variables over $k$ and a natural number $h$ such that $\rho$ is a homomorphism $\Phi \to \Phi'$ of formal group laws commuting with all $\mathrm{act}(a)$ and with $\mathrm{varpi}$, and the kernel algebra of $\rho$ is finite and projective over $k$ of rank $p^h$ after base change along every ring homomorphism from $k$ to a field. (The finiteness clause in particular rules out $\rho = 0$.) The integer $h$ is not constrained further here.
--
--   This is the uniqueness, or isogeny, half of the classification of special formal $\mathcal O_D$-modules of height $4$ over an algebraically closed field of characteristic $p$, as in Drinfeld's work and Boutot–Carayol II (5.2), which makes the base point of Drinfeld's moduli problem well defined up to isogeny. It is used by the refinement producing isogenies of height divisible by $4$ and by the combined statement on non-emptiness, isogeny and the centraliser of the $\mathcal O_D$-action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_exists_isIsogenyOfHeight_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.SpecialFormalODModule.exists_isIsogenyOfHeight_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (j : CerednikDrinfeld.Zp2 p →+* k) (Φ Φ' : CerednikDrinfeld.SpecialFormalODModule p j) :
    ∃ (ρ : CerednikDrinfeld.SpecialFormal.Series k) (h : ℕ),
      CerednikDrinfeld.FormalODModule.IsIsogenyOfHeight Φ.toFormalODModule Φ'.toFormalODModule
        ρ h := by sorry
