-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_addMonoidHom_bijective_map_eq_of_hasStructureConstants
-- name    : CerednikDrinfeld.FormalODModule.exists_addMonoidHom_bijective_map_eq_of_hasStructureConstants
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/36179c6c-55f9-5fed-91bd-ae55faa63498
-- title:
--   Equal Pi-structure constants force an isomorphism of Cartier modules
-- statement:
--   Let $p$ be a prime and $B$ a commutative ring equipped with a ring homomorphism $j$ from $\mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2})$ to $B$, and assume $B$ is Hausdorff for the ideal $(p)$, i.e. an element congruent to $0$ modulo $p^n$ for every $n$ vanishes. Let $X$ and $X'$ be formal $\mathcal{O}_D$-modules over $B$, each consisting of a commutative two-dimensional formal group law $F$ over $B$, an action of $\mathbb{Z}_{p^2}$ by law endomorphisms which is additive and multiplicative with $\mathrm{act}(1)=\mathrm{id}$, and a law endomorphism $\varpi$ satisfying $\varpi\circ\varpi=\mathrm{act}(p)$ and $\varpi\circ\mathrm{act}(a)=\mathrm{act}(\sigma a)\circ\varpi$ for the Witt–Frobenius $\sigma$. Let $\gamma$, respectively $\gamma'$, be a pair of elements of the Cartier module of $X.F$, respectively $X'.F$, which is a homogeneous $V$-basis for $j$: $\gamma_i$ lies in the $i$-th graded piece, meaning $\mathrm{endAct}(\mathrm{actEnd}(\tau(c)))\,\gamma_i = \langle j(\tau(c))^{p^i}\rangle\,\gamma_i$ for every $c\in\mathbb{F}_{p^2}$ and its Teichmüller lift $\tau(c)$, and the matrix of tangent coordinates $(\mathrm{tangent}(\gamma_i)_k)$ has unit determinant. Let $a:\mathbb{N}\to\mathrm{Fin}\,2\to B$ be a family that is a system of structure constants for both bases: for each $i$ and each $N$ there is $h$ with $\mathrm{endAct}(\varpi)\,\gamma_i=\sum_{m<N}V^m\big(\langle a_{m,i}\rangle\,\gamma_{\mathrm{piIndex}(m,i)}\big)+V^N h$, where $\mathrm{piIndex}(m,i)\equiv m+i+1 \pmod 2$ and $V$ denotes `verschiebungInt`, and likewise for $X'$, $\gamma'$. Then there exists an additive homomorphism $\theta$ from the Cartier module of $X.F$ to that of $X'.F$ which is bijective, sends $\gamma_i$ to $\gamma'_i$ for $i=0,1$, and commutes with `frobenius`, with `verschiebungInt`, with the homothety $\langle b\rangle$ for every $b\in B$, with the action of every $c\in\mathbb{Z}_{p^2}$ (i.e. $\theta\circ\mathrm{endAct}(X.\mathrm{actEnd}\,c)=\mathrm{endAct}(X'.\mathrm{actEnd}\,c)\circ\theta$) and with $\varpi$.
--
--   This is the Cartier-module form of the uniqueness up to isomorphism of special formal $\mathcal{O}_D$-modules with prescribed structure constants for $\Pi$ (Boutot–Carayol, chap. II, Prop. (2.3)): all the content of that uniqueness statement is carried here by an additive bijection of Cartier modules compatible with $F$, $V$, homotheties and the $\mathcal{O}_D$-action. It is used to produce an isomorphism of formal $\mathcal{O}_D$-modules in [`CerednikDrinfeld.FormalODModule.exists_hom_isIso_forall_map_eq_of_hasStructureConstants`](thm.html#CerednikDrinfeld.FormalODModule.exists_hom_isIso_forall_map_eq_of_hasStructureConstants).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_addMonoidHom_bijective_map_eq_of_hasStructureConstants.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.exists_addMonoidHom_bijective_map_eq_of_hasStructureConstants
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (hsep : IsHausdorff (Ideal.span {(p : B)}) B)
    (X X' : CerednikDrinfeld.FormalODModule p B)
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F)
    (γ' : Fin 2 → MvFormalGroup.CartierModule p X'.F)
    (hγ : X.IsHomogeneousVBasis j γ) (hγ' : X'.IsHomogeneousVBasis j γ')
    (a : ℕ → Fin 2 → B)
    (ha : X.HasStructureConstants γ a) (ha' : X'.HasStructureConstants γ' a) :
    ∃ θ : MvFormalGroup.CartierModule p X.F →+ MvFormalGroup.CartierModule p X'.F,
      Function.Bijective θ ∧ (∀ i : Fin 2, θ (γ i) = γ' i) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.frobenius f) =
        MvFormalGroup.CartierModule.frobenius (θ f)) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.verschiebungInt f) =
        MvFormalGroup.CartierModule.verschiebungInt (θ f)) ∧
      (∀ (b : B) f, θ (MvFormalGroup.CartierModule.homothety b f) =
        MvFormalGroup.CartierModule.homothety b (θ f)) ∧
      (∀ (c : CerednikDrinfeld.Zp2 p) f,
        θ (MvFormalGroup.CartierModule.endAct (X.actEnd c) f) =
          MvFormalGroup.CartierModule.endAct (X'.actEnd c) (θ f)) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.endAct X.varpiEnd f) =
        MvFormalGroup.CartierModule.endAct X'.varpiEnd (θ f)) := by sorry
