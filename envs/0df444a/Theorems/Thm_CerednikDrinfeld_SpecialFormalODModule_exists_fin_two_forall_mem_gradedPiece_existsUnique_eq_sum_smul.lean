-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_forall_mem_gradedPiece_existsUnique_eq_sum_smul
-- name    : CerednikDrinfeld.SpecialFormalODModule.exists_fin_two_forall_mem_gradedPiece_existsUnique_eq_sum_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/f78dbfb6-8385-533a-9ac6-0be2777d7ff6
-- title:
--   Graded pieces of a special formal mathcal O_D-module: free of rank 2
-- statement:
--   Let $p$ be a prime and $k$ a perfect field of characteristic $p$ (perfection in the sense of `PerfectRing k p`), let $j\colon \mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2}) \to k$ be a ring homomorphism, and let $\Phi$ be a special formal $\mathcal O_D$-module over $k$ relative to $j$, that is: a $2$-dimensional formal group law $\Phi.F$ over $k$ together with commutativity, an action $a \mapsto \Phi.\mathrm{act}\,a$ of $\mathbb{Z}_{p^2}$ by endomorphisms of the law which is multiplicative, additive and unital, and a series $\Phi.\mathrm{varpi}$, an endomorphism of the law, satisfying $\varpi \circ \varpi = \mathrm{act}(p)$ and $\varpi \circ \mathrm{act}(a) = \mathrm{act}(\sigma a) \circ \varpi$ for the Witt-vector Frobenius $\sigma$, subject to the speciality condition (the two Lie eigenspaces `lieZero j`, `lieOne j` are complements and each is an invertible $k$-module) and to $\mathrm{act}(p)$ having kernel of degree $p^4$. Fix $n \in \mathbb{N}$ and let $M_n = \Phi.\mathrm{gradedPiece}\,j\,n$ be the additive subgroup of the Cartier module $\mathrm{CartierModule}\,p\,\Phi.F$ consisting of those $f$ with $\mathrm{endAct}(\Phi.\mathrm{actEnd}\,[c])\,f = \mathrm{homothety}\,(j([c])^{p^n})\,f$ for every $c \in \mathbb{F}_{p^2}$, where $[c]$ is the Teichmüller representative. The theorem asserts two things: first, $M_n$ is stable under the $W(k)$-action, i.e. $w \cdot f \in M_n$ for all $w \in W(k)$ and $f \in M_n$; second, there is a family $e \colon \mathrm{Fin}\,2 \to \mathrm{CartierModule}\,p\,\Phi.F$ with $e_r \in M_n$ for both $r$ such that every $f \in M_n$ is $f = \sum_r w_r \cdot e_r$ for a unique pair $w \colon \mathrm{Fin}\,2 \to W(k)$. Freeness of rank $2$ is thus expressed as unique representability by two distinguished elements rather than by producing a `Module.Basis` term.
--
--   This is the first structural step in Drinfeld's classification of special formal $\mathcal O_D$-modules of height $4$, as carried out in Boutot–Carayol (proof of Proposition 5.1 of Chapter II): the Cartier–Dieudonné module splits into its two graded pieces for the $\mathbb{Z}_{p^2}$-action, each of which is a $W(k)$-lattice of rank $2$. It is used downstream for the injectivity and bijectivity statements about the action of $\varpi$ and of $V^{-1}\varpi$ on the graded pieces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_forall_mem_gradedPiece_existsUnique_eq_sum_smul.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.SpecialFormalODModule.exists_fin_two_forall_mem_gradedPiece_existsUnique_eq_sum_smul
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectRing k p]
    (j : CerednikDrinfeld.Zp2 p →+* k) (Φ : CerednikDrinfeld.SpecialFormalODModule p j) (n : ℕ) :
    (∀ (w : WittVector p k) (f : MvFormalGroup.CartierModule p Φ.F),
        f ∈ Φ.gradedPiece j n → w • f ∈ Φ.gradedPiece j n) ∧
    ∃ e : Fin 2 → MvFormalGroup.CartierModule p Φ.F,
      (∀ r, e r ∈ Φ.gradedPiece j n) ∧
      ∀ f ∈ Φ.gradedPiece j n, ∃! w : Fin 2 → WittVector p k, f = ∑ r, w r • e r := by sorry
