-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_addMonoidHom_cartierModule_injective_of_isAlgClosed
-- name    : CerednikDrinfeld.SpecialFormalODModule.exists_addMonoidHom_cartierModule_injective_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/885f9eb1-bd9e-5c71-bc4a-80be491c7e0a
-- title:
--   Cartier modules of special formal mathcal O_D-modules are isogenous
-- statement:
--   Let $p$ be a prime, $k$ an algebraically closed field of characteristic $p$, and $j\colon \mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2}) \to k$ a ring homomorphism. Let $\Phi$ and $\Phi'$ be special formal $\mathcal O_D$-modules over $k$ relative to $j$: each consists of a two-dimensional formal group law $F$ over $k$ that is commutative, power series $\mathrm{act}(a)$ for $a \in \mathbb{Z}_{p^2}$ and $\varpi$, all endomorphisms of the law, with $\mathrm{act}(1)$ the identity, $\mathrm{act}(ab) = \mathrm{act}(a)\circ\mathrm{act}(b)$, $\mathrm{act}(a+b)$ the sum of $\mathrm{act}(a)$ and $\mathrm{act}(b)$ formed via $F$, $\varpi\circ\varpi = \mathrm{act}(p)$ and $\varpi\circ\mathrm{act}(a) = \mathrm{act}(\sigma a)\circ\varpi$ for the Witt-vector Frobenius $\sigma$; together with speciality (the two Lie subspaces $\mathrm{lieZero}\,j$ and $\mathrm{lieOne}\,j$ are complementary and each invertible as a $k$-module) and height $4$ (the endomorphism $\mathrm{act}(p)$ has finite kernel of degree $p^4$). The assertion is that there is an additive map $\theta$ from the Cartier module of $\Phi.F$ to that of $\Phi'.F$ which is injective; commutes with `frobenius`, with `verschiebung`, with the homothety by every $a \in k$, with the operator induced by $\mathrm{act}(a)$ for every $a \in \mathbb{Z}_{p^2}$ (that of $\Phi$ on the source, that of $\Phi'$ on the target), and likewise with the operator induced by $\varpi$; and for which there exists $N \in \mathbb{N}$ such that $p^N g$ lies in the image of $\theta$ for every element $g$ of the target.
--
--   This is the Cartier–Dieudonné module form of the statement that special formal $\mathcal O_D$-modules of height $4$ over an algebraically closed field of characteristic $p$ form a single isogeny class, as used in the Čerednik–Drinfeld uniformisation: the two Cartier modules become isomorphic, compatibly with $F$, $V$, the homotheties and the $\mathcal O_D$-action, after multiplication by a power of $p$. It is the input to the construction of an actual isogeny of special formal $\mathcal O_D$-modules ([`CerednikDrinfeld.SpecialFormalODModule.exists_isIsogenyOfHeight_of_isAlgClosed`](thm.html#CerednikDrinfeld.SpecialFormalODModule.exists_isIsogenyOfHeight_of_isAlgClosed)) and to the comparison of endomorphism rings ([`CerednikDrinfeld.SpecialFormalODModule.exists_ringHom_centralizer_injective_of_isAlgClosed`](thm.html#CerednikDrinfeld.SpecialFormalODModule.exists_ringHom_centralizer_injective_of_isAlgClosed)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_exists_addMonoidHom_cartierModule_injective_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.SpecialFormalODModule.exists_addMonoidHom_cartierModule_injective_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (j : CerednikDrinfeld.Zp2 p →+* k) (Φ Φ' : CerednikDrinfeld.SpecialFormalODModule p j) :
    ∃ θ : MvFormalGroup.CartierModule p Φ.F →+ MvFormalGroup.CartierModule p Φ'.F,
      Function.Injective θ ∧
      (∀ f, θ (MvFormalGroup.CartierModule.frobenius f) =
        MvFormalGroup.CartierModule.frobenius (θ f)) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.verschiebung f) =
        MvFormalGroup.CartierModule.verschiebung (θ f)) ∧
      (∀ (a : k) f, θ (MvFormalGroup.CartierModule.homothety a f) =
        MvFormalGroup.CartierModule.homothety a (θ f)) ∧
      (∀ (a : CerednikDrinfeld.Zp2 p) f,
        θ (MvFormalGroup.CartierModule.endAct (Φ.actEnd a) f) =
          MvFormalGroup.CartierModule.endAct (Φ'.actEnd a) (θ f)) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.endAct Φ.varpiEnd f) =
        MvFormalGroup.CartierModule.endAct Φ'.varpiEnd (θ f)) ∧
      ∃ N : ℕ, ∀ g : MvFormalGroup.CartierModule p Φ'.F,
        ∃ f : MvFormalGroup.CartierModule p Φ.F, θ f = p ^ N • g := by sorry
