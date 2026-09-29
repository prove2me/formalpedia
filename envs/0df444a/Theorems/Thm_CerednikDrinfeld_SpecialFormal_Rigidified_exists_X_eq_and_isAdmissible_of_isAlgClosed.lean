-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_X_eq_and_isAdmissible_of_isAlgClosed
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_X_eq_and_isAdmissible_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/63457cbf-2906-5877-ab06-9e17703f2e67
-- title:
--   Rigidifying special formal mathcal O_D-modules over algebraically closed fields
-- statement:
--   Let $p$ be a prime, $O$ a commutative ring with a ring homomorphism $\iota\colon \mathbb Z_{p^2}=W(\mathbb F_{p^2})\to O$, and let $\Phi$ be a `FormalODModule` over $O/pO$, that is, a commutative two-dimensional formal group law $F$ together with series $\mathrm{act}(a)$ for $a\in\mathbb Z_{p^2}$ and a series $\varpi$, all endomorphisms of the law, with $\mathrm{act}(1)=\mathrm{id}$, $\mathrm{act}$ multiplicative and additive for the group law, $\varpi\circ\varpi=\mathrm{act}(p)$ and $\varpi\circ\mathrm{act}(a)=\mathrm{act}(\sigma a)\circ\varpi$ for the Witt-vector Frobenius $\sigma$. Let $k$ be an algebraically closed field of characteristic $p$ and $\psi\colon O\to k$ a ring homomorphism. Assume the base change of $\Phi$ along `residueMap ψ` $\colon O/pO\to k/pk$ is special with respect to $\mathbb Z_{p^2}\to k/pk$ induced by $\iota$ and $\psi$ — its Lie algebra splits as two complementary invertible submodules `lieZero` and `lieOne` — and has height $4$, i.e. $\mathrm{act}(p)$ has kernel of degree $p^4$. Then for every special formal $\mathcal O_D$-module $X$ of height $4$ over $k$, special for $\psi\circ\iota$, there is a triple $t=(t.X,n,\rho)$ consisting of a formal $\mathcal O_D$-module over $k$, a natural number and a series over $k/pk$, with $t.X$ equal to the underlying module of $X$, such that $t.X$ is special for $\psi\circ\iota$, of height $4$, and $\rho$ is an isogeny of height $4n$ from the reduction `t.Φbar ψ` of $\Phi$ to the reduction `t.Xbar` of $t.X$ modulo $p$.
--
--   This is the surjectivity of the forgetful map from Drinfeld's moduli functor of rigidified special formal $\mathcal O_D$-modules to isomorphism classes of special formal $\mathcal O_D$-modules of height $4$ over an algebraically closed field of characteristic $p$: any such module admits a rigidification by an isogeny of height divisible by $4$ from the fixed module $\Phi$. It feeds the construction of the moduli package and the verification that the associated functor is a Zariski sheaf with the expected identification of its points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_X_eq_and_isAdmissible_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_X_eq_and_isAdmissible_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] {O : Type v} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (k : Type u) [Field k] [IsAlgClosed k] [CharP k p] (ψ : O →+* k)
    (hΦ : (Φ.map (residueMap ψ)).IsSpecial
      ((residueMap ψ).comp ((Ideal.Quotient.mk (pIdeal p O)).comp ι)))
    (hΦ4 : (Φ.map (residueMap ψ)).HasHeight 4)
    (X : SpecialFormalODModule p (structureMap ι ψ)) :
    ∃ t : Rigidified p Φ k, t.X = X.toFormalODModule ∧ t.IsAdmissible ι ψ := by sorry
