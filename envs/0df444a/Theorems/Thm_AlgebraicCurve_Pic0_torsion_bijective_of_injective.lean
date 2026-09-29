-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_torsion_bijective_of_injective
-- name    : AlgebraicCurve.Pic0.torsion.bijective_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/6562c502-d9e3-5fae-ad8b-402b327e1910
-- title:
--   Injective maps into the character group of Pic⁰[n] are bijective
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $n$ be a natural number with $n \neq 0$. Write $\mathrm{Div}(K,F)$ for the group of finitely supported $\mathbb{Z}$-valued functions on the places `Place K F`, $\mathrm{Pic}^0(K,F)$ for the quotient of the kernel of the degree map by the subgroup of principal divisors inside it, and $\mathrm{Pic}^0(K,F)[n]$ for its $n$-torsion subgroup, i.e. the elements annihilated by $n$ as a $\mathbb{Z}$-module. Assume that $K$ has enough $n$-th roots of unity in the sense of `HasEnoughRootsOfUnity`, and that the group $\mathrm{Pic}^0(K,F)[n]$ is finite. Let $f$ be a homomorphism of additive groups from $\mathrm{Pic}^0(K,F)[n]$ to the additive group underlying `HomPic0Gm K F n`, the group of additive characters of $\mathrm{Pic}^0(K,F)[n]$ with values in the multiplicative monoid of $K$. The assertion is that if $f$ is injective, then $f$ is bijective. No compatibility of $f$ with any pairing is assumed: the statement is purely a counting statement about the two groups.
--
--   This is the standard upgrade of non-degeneracy to perfectness for a pairing into the multiplicative group, resting on the Pontryagin-type count of characters of a finite abelian group over a field containing enough roots of unity. It is used in the proof of [`AlgebraicCurve.DivisorialWeilPairingData.perfect_of_divisible_coprime_of_isAlgClosed`](thm.html#AlgebraicCurve.DivisorialWeilPairingData.perfect_of_divisible_coprime_of_isAlgClosed), where an injective map induced by the divisorial Weil pairing on $\mathrm{Pic}^0[n]$ is thereby shown to be an isomorphism onto the character group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_torsion_bijective_of_injective.lean

import Definitions.Def_AlgebraicCurve_JacobianH1Autoduality
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Pic0.torsion.bijective_of_injective {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n] [Finite (Pic0.torsion K F n)] (f : Pic0.torsion K F n →+ Additive (HomPic0Gm K F n)) (hf : Function.Injective f) :
    Function.Bijective f := by sorry
