-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent
-- name    : CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/63c9a8fe-6332-5263-ac21-336b50838d0d
-- title:
--   Splitting of the Cartier module into graded pieces 0 and 1
-- statement:
--   Let $p$ be a prime, let $B$ be a commutative ring, let $j\colon W(\mathbb F_{p^2})\to B$ be a ring homomorphism (here `Zp2 p` is the Witt ring $W(\mathbb F_{p^2})$, written as `WittVector p (GaloisField p 2)`), assume $p$ is nilpotent in $B$, and let $X$ be a formal $\mathcal O_D$-module over $B$ in the sense of the structure `FormalODModule`: a commutative two-dimensional formal group law $F$ over $B$ together with power-series endomorphisms $\mathrm{act}(a)$ of $F$ for $a\in W(\mathbb F_{p^2})$ and a further endomorphism $\varpi$, such that $\mathrm{act}$ is multiplicative and additive for the group law, $\mathrm{act}(1)$ is the identity, $\varpi\circ\varpi=\mathrm{act}(p)$ and $\varpi\circ\mathrm{act}(a)=\mathrm{act}(\sigma a)\circ\varpi$ with $\sigma$ the Witt-vector Frobenius. For $n\in\mathbb N$ the subgroup $X.\mathrm{gradedPiece}\,j\,n$ of the Cartier module $\mathrm{CartierModule}\,p\,X.F$ consists of those $f$ with $\mathrm{endAct}(X.\mathrm{actEnd}([c]))f=\langle j([c])^{p^n}\rangle f$ for every $c\in\mathbb F_{p^2}$, where $[c]$ is the Teichmüller lift, $\mathrm{endAct}$ is the induced action of endomorphisms of $F$ on the Cartier module and $\langle\,\cdot\,\rangle$ denotes the homothety by an element of $B$. The assertion is that $X.\mathrm{gradedPiece}\,j\,0$ and $X.\mathrm{gradedPiece}\,j\,1$ are complements of one another in the lattice of additive subgroups of $\mathrm{CartierModule}\,p\,X.F$: their intersection is zero and their sum is the whole Cartier module.
--
--   This is the decomposition of the Cartier module of a formal $\mathcal O_D$-module into the two eigen-pieces for the Teichmüller action of $\mathbb F_{p^2}^\times$, as in Boutot–Carayol II (2.2). It underlies the subsequent analysis of special formal modules, and is cited throughout the study of the graded pieces, of the action of $\varpi$ on them, and of height and reducedness conditions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent.lean

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

theorem CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (hB : IsNilpotent (p : B)) (X : CerednikDrinfeld.FormalODModule p B) :
    IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1) := by sorry
