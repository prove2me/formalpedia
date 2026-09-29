-- Prove2me | Theorems.Thm_ExtCitation_coe_cycloChar_primeLocalToGlobal_eq_natCast_of_isFrobeniusAt
-- name    : ExtCitation.coe_cycloChar_primeLocalToGlobal_eq_natCast_of_isFrobeniusAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/af4246e9-ea20-539c-b5d4-6564cd49b7a5
-- title:
--   Mod-p cyclotomic character of a Frobenius at q ≠ p
-- statement:
--   Let $p$ be a prime and let $q$ be a prime with $q \neq p$ as natural numbers. Let $\varphi$ be an element of the local Galois group at $q$, that is, of $\mathrm{Aut}_{\mathbb{Q}_q}$ of the chosen algebraic closure `PadicAlgCl` $q$ of $\mathbb{Q}_q$, and let $\sigma :=$ `primeLocalToGlobal` $q\,\varphi$ denote its image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, obtained by restricting scalars to $\mathbb{Q}$ and then restricting the resulting automorphism to the normal subextension $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. Write $A$ for the valuation subring `primeLocalPlace` $q$ of $\overline{\mathbb{Q}}$, namely the preimage of $\mathbb{Z}_q$ under the fixed embedding of $\overline{\mathbb{Q}}$ into `PadicAlgCl` $q$. Assume that $\sigma$ is an arithmetic Frobenius at $A$ with exponent $q$, in the sense that $\sigma$ belongs to the decomposition subgroup of $A$ over $\mathbb{Q}$ and the induced action on the residue field of $A$ is $x \mapsto x^{q}$. Then the value of the mod-$p$ cyclotomic character `cycloChar` $p$ at $\sigma$, an element of $(\mathbb{Z}/p)^{\times}$, has image $q \bmod p$ in $\mathbb{Z}/p$.
--
--   This is the standard computation $\chi_p(\mathrm{Frob}_q) = q$ for $q \neq p$, here in the form attached to the project's fixed local-to-global data at $q$. It is what identifies, for an unramified module $M$, the $q$-eigenspace of Frobenius with the invariants of a Tate twist, and it is used in the comparison of continuous cohomology classes with invariants and dual twists, and in the Selmer-group bound involving Taylor–Wiles primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_coe_cycloChar_primeLocalToGlobal_eq_natCast_of_isFrobeniusAt.lean

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem ExtCitation.coe_cycloChar_primeLocalToGlobal_eq_natCast_of_isFrobeniusAt
    (p : ℕ) [Fact p.Prime] (q : Nat.Primes) (hqp : (q : ℕ) ≠ p)
    {φ : primeLocalGaloisGroup q}
    (hφ : (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q) :
    ((cycloChar p (primeLocalToGlobal q φ) : (ZMod p)ˣ) : ZMod p) = ((q : ℕ) : ZMod p) := by sorry
