-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_CritChart_exists_basis_coe_eq_and_injective_endMatrix_of_forall_existsUnique_of_isCompl
-- name    : CerednikDrinfeld.FormalODModule.CritChart.exists_basis_coe_eq_and_injective_endMatrix_of_forall_existsUnique_of_isCompl
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/b80871af-8bd6-5b65-b7e7-6e31e87ecae6
-- title:
--   Invariant frame yields ℤₚ-basis and injective endomorphism matrix
-- statement:
--   Let $p$ be a prime and $B$ a commutative integral domain of characteristic $p$, let $j\colon W(\mathbb F_{p^2})\to B$ be a ring homomorphism, and let $X$ be a formal $\mathcal O_D$-module over $B$: a commutative two-dimensional formal group law $X.F$ together with an action of $W(\mathbb F_{p^2})$ by endomorphisms of the law and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi=[p]$ and $\varpi\circ[a]=[\sigma a]\circ\varpi$. Assume the two submodules of $\operatorname{Lie}X$ on which every $a$ acts by $j(a)$, respectively by $j(\sigma a)$, are complementary. Fix $i\in\mathbb N$ and a finite index type $\iota$, and let $e\colon\iota\to M$ be a family in the Cartier module $M$ of $X.F$ such that each $e_r$ lies in the degree-$i$ invariants, i.e. $\,[\,\omega\,]$ acts on $e_r$ as the homothety by $j(\omega)^{p^i}$ for every Teichmüller lift $\omega$ of an element of $\mathbb F_{p^2}$ and $\varpi_*e_r=Ve_r$. Assume further that every $m$ in the degree-$i$ graded piece is uniquely of the form $\sum_r w_r\cdot e_r$ with $w\colon\iota\to W(B)$, and that $\sum_r w_r\cdot e_r$ is invariant precisely when each $w_r$ is fixed by the Witt vector Frobenius. Then there is a basis $\beta$ of the $\mathbb Z_p$-module of degree-$i$ invariants, indexed by $\iota$, with $\beta_r=e_r$ in $M$, such that the ring homomorphism `CritChart.endMatrix` sending an element of the centraliser of the $W(\mathbb F_{p^2})$-action and of $\varpi$ in $\operatorname{End}(X.F)$ to the matrix of its induced action in the basis $\beta$ is injective, its composite `CritChart.endMatrixQ` with the entrywise inclusion $\mathbb Z_p\subset\mathbb Q_p$ is injective as well, and each value of the latter is the entrywise image of a matrix over $\mathbb Z_p$.
--
--   This is the injectivity half of Boutot–Carayol's identification of the $\mathcal O_D$-endomorphism algebra of a special formal module with a matrix algebra, read on a critical chart where the degree-$i$ invariants of the Cartier module provide the relevant lattice. It is used in the statement producing, over an algebraically closed base, a critical index together with a basis for which the endomorphism matrix map is injective with integral values.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_CritChart_exists_basis_coe_eq_and_injective_endMatrix_of_forall_existsUnique_of_isCompl.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart
import Definitions.Def_CerednikDrinfeld_CritChartEndMatrix

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.FormalODModule MvFormalGroup
open MvFormalGroup.CartierModule

theorem CerednikDrinfeld.FormalODModule.CritChart.exists_basis_coe_eq_and_injective_endMatrix_of_forall_existsUnique_of_isCompl
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] [CharP B p] [IsDomain B]
    (j : CerednikDrinfeld.Zp2 p →+* B) (X : CerednikDrinfeld.FormalODModule p B)
    (hLie : IsCompl (X.lieZero j) (X.lieOne j)) (i : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι → MvFormalGroup.CartierModule p X.F)
    (he : ∀ r, e r ∈ CritChart.invariants X j i)
    (hrepr : ∀ m ∈ X.gradedPiece j i, ∃! w : ι → WittVector p B, m = ∑ r, w r • e r)
    (hfix : ∀ w : ι → WittVector p B,
      (∑ r, w r • e r) ∈ CritChart.invariants X j i ↔ ∀ r, WittVector.frobenius (w r) = w r) :
    ∃ β : Module.Basis ι ℤ_[p] (CritChart.invariantsSubmodule X j i),
      (∀ r, (β r : MvFormalGroup.CartierModule p X.F) = e r) ∧
      Function.Injective (CritChart.endMatrix X j i β) ∧
      Function.Injective (CritChart.endMatrixQ X j i β) ∧
      (∀ f, ∃ A : Matrix ι ι ℤ_[p], CritChart.endMatrixQ X j i β f = A.map ((↑) : ℤ_[p] → ℚ_[p])) := by sorry
