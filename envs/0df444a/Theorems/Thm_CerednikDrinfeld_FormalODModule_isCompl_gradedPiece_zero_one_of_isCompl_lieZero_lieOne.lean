-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne
-- name    : CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/9cdd19de-35aa-5038-9704-78485bd686ce
-- title:
--   ℤ/2-grading of the Cartier module of a formal mathcal O_D-module
-- statement:
--   Let $p$ be a prime, $B$ a commutative ring of characteristic $p$, and $j\colon \mathbb Z_{p^2}=W(\mathbb F_{p^2})\to B$ a ring homomorphism. Let $X$ be a formal $\mathcal O_D$-module over $B$ in the sense of the project structure: a commutative two-dimensional formal group law $X.F$ together with series $a\mapsto X.\mathrm{act}\,a$ ($a\in\mathbb Z_{p^2}$) and $X.\mathrm{varpi}$ that are endomorphisms of the law, additive and multiplicative in $a$, with $\mathrm{varpi}\circ\mathrm{varpi}=\mathrm{act}\,p$ and $\mathrm{varpi}\circ\mathrm{act}\,a=\mathrm{act}(\sigma a)\circ\mathrm{varpi}$ for the Witt–Frobenius $\sigma$; write $X.\mathrm{actEnd}\,a$ and $X.\mathrm{varpiEnd}$ for the resulting endomorphisms. For $n\in\mathbb N$ let $M_n=X.\mathrm{gradedPiece}\;j\;n$ be the additive subgroup of the Cartier module $M=\mathrm{CartierModule}\;p\;X.F$ of those $f$ with $\mathrm{endAct}(X.\mathrm{actEnd}[c])f=\mathrm{homothety}\bigl(j([c])^{p^n}\bigr)f$ for every $c\in\mathbb F_{p^2}$, $[c]$ denoting the Teichmüller representative. Assume that the submodules $X.\mathrm{lieZero}\;j=\bigcap_a\ker(X.\mathrm{lieAct}\,a-j(a)\cdot\mathrm{id})$ and $X.\mathrm{lieOne}\;j=\bigcap_a\ker(X.\mathrm{lieAct}\,a-j(\sigma a)\cdot\mathrm{id})$ of $X.\mathrm{Lie}$ are complements of each other. Then eight assertions hold: $M_0$ and $M_1$ are complementary additive subgroups of $M$; for all $n$ and all $g\in M$, $Vg\in M_{n+1}$ if and only if $g\in M_n$; $F(M_n)\subseteq M_{n+1}$; $\mathrm{endAct}(X.\mathrm{varpiEnd})(M_n)\subseteq M_{n+1}$; $\mathrm{homothety}(b)(M_n)\subseteq M_n$ for every $b\in B$; $\mathrm{endAct}(X.\mathrm{actEnd}\,a)(M_n)\subseteq M_n$ for every $a\in\mathbb Z_{p^2}$; and the images of $M_0$ and $M_1$ under the tangent map are the additive subgroups underlying $X.\mathrm{lieZero}\;j$ and $X.\mathrm{lieOne}\;j$ respectively.
--
--   This is the $\mathbb Z/2\mathbb Z$-grading of the Cartier module of a formal $\mathcal O_D$-module induced by the action of the unramified quadratic subring $\mathbb Z_{p^2}\subset\mathcal O_D$, here phrased on Teichmüller representatives so that only the homotheties of the Cartier module occur, together with the compatibility of the grading with $V$, $F$, $\Pi$ and the tangent map. It underlies the subsequent analysis of critical charts and of special formal $\mathcal O_D$-modules, being cited in the construction of adapted bases and in the criteria for criticality.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] [CharP B p]
    (j : CerednikDrinfeld.Zp2 p →+* B) (X : CerednikDrinfeld.FormalODModule p B)
    (hLie : IsCompl (X.lieZero j) (X.lieOne j)) :
    IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1) ∧
    (∀ (n : ℕ) (g : MvFormalGroup.CartierModule p X.F),
        MvFormalGroup.CartierModule.verschiebung g ∈ X.gradedPiece j (n + 1) ↔
          g ∈ X.gradedPiece j n) ∧
    (∀ n, ∀ f ∈ X.gradedPiece j n,
        MvFormalGroup.CartierModule.frobenius f ∈ X.gradedPiece j (n + 1)) ∧
    (∀ n, ∀ f ∈ X.gradedPiece j n,
        MvFormalGroup.CartierModule.endAct X.varpiEnd f ∈ X.gradedPiece j (n + 1)) ∧
    (∀ (n : ℕ) (b : B), ∀ f ∈ X.gradedPiece j n,
        MvFormalGroup.CartierModule.homothety b f ∈ X.gradedPiece j n) ∧
    (∀ (n : ℕ) (a : CerednikDrinfeld.Zp2 p), ∀ f ∈ X.gradedPiece j n,
        MvFormalGroup.CartierModule.endAct (X.actEnd a) f ∈ X.gradedPiece j n) ∧
    (X.gradedPiece j 0).map MvFormalGroup.CartierModule.tangent = (X.lieZero j).toAddSubgroup ∧
    (X.gradedPiece j 1).map MvFormalGroup.CartierModule.tangent = (X.lieOne j).toAddSubgroup := by sorry
