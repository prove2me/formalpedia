-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hasKernelOfDegree_pow_two_mul_of_mul_eq_natCast_of_isSpecial_of_hasHeight
-- name    : CerednikDrinfeld.FormalODModule.exists_hasKernelOfDegree_pow_two_mul_of_mul_eq_natCast_of_isSpecial_of_hasHeight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/132850ce-ae58-5c23-9c08-9f136c49355e
-- title:
--   Even kernel degree for a factor of [r^M] on a special formal module
-- statement:
--   Let $r$ be a prime and $k$ an algebraically closed field of characteristic $r$, let $j : \mathbb{Z}_{r^2} \to k$ be a ring homomorphism, where $\mathbb{Z}_{r^2}$ denotes the Witt vectors of the field with $r^2$ elements, and let $\Phi$ be a formal $\mathcal{O}_D$-module over $k$: a commutative two-dimensional formal group law $\Phi.F$ together with an action $a \mapsto \Phi.\mathrm{act}\,a$ of $\mathbb{Z}_{r^2}$ by endomorphisms of the law and an endomorphism $\Phi.\mathrm{varpi}$ satisfying $\mathrm{varpi} \circ \mathrm{varpi} = \mathrm{act}\,r$ and $\mathrm{varpi} \circ \mathrm{act}\,a = \mathrm{act}(\sigma a) \circ \mathrm{varpi}$ for the Witt vector Frobenius $\sigma$. Assume $\Phi$ is special for $j$, i.e. the Lie algebra of $\Phi$ is the direct sum of the submodule on which each $a$ acts by $j(a)$ and the submodule on which each $a$ acts by $j(\sigma a)$, both invertible $k$-modules, and that $\Phi$ has height $4$, i.e. $\mathrm{act}\,r$ has kernel of degree $r^4$. Let $e, e'$ lie in the centraliser, inside $\mathrm{End}(\Phi.F)$, of the set consisting of all $\Phi.\mathrm{actEnd}\,a$ together with $\Phi.\mathrm{varpiEnd}$, and suppose $e e' = r^M$ in that centraliser for some natural number $M$. Then there is $m'$ such that the pair of power series underlying $e'$ has kernel of degree $r^{2m'}$: its kernel algebra is a finite projective $k$-module whose rank, after base change along any ring homomorphism from $k$ to a field, equals $r^{2m'}$.
--
--   This is the degree-parity statement for $\mathcal{O}_D$-linear isogenies of special formal modules of height $4$ in the Cerednik–Drinfeld setting: a factor of multiplication by $r^M$ automatically has finite locally free kernel, of degree an even power of $r$. It is used in the treatment of isogeny pairs and Atkin–Lehner data for fake elliptic curves, where the kernel degree of a transported isogeny must be recognised as an even power of the residue characteristic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_hasKernelOfDegree_pow_two_mul_of_mul_eq_natCast_of_isSpecial_of_hasHeight.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.exists_hasKernelOfDegree_pow_two_mul_of_mul_eq_natCast_of_isSpecial_of_hasHeight
    (r : ℕ) [Fact r.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k r]
    (j : Zp2 r →+* k) (Φ : FormalODModule r k) (hΦs : Φ.IsSpecial j) (hΦ4 : Φ.HasHeight 4)
    (e e' : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})))
    (M : ℕ) (hee' : e * e' = ((r ^ M : ℕ) : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})))) :
    ∃ m' : ℕ, FormalODModule.HasKernelOfDegree ((e' : MvFormalGroup.End Φ.F).toPowerSeries) (r ^ (2 * m')) := by sorry
