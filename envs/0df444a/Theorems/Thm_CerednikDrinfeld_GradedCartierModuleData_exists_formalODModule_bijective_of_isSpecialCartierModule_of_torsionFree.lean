-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_formalODModule_bijective_of_isSpecialCartierModule_of_torsionFree
-- name    : CerednikDrinfeld.GradedCartierModuleData.exists_formalODModule_bijective_of_isSpecialCartierModule_of_torsionFree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/90794aa3-4bdb-5761-9a82-9379f597b3e7
-- title:
--   Every special graded Cartier datum comes from a formal 𝒪_D-module
-- statement:
--   Fix a prime $p$, a commutative ring $B$ and a ring homomorphism $j : W(\mathbb{F}_{p^2}) \to B$, and assume $B$ is $p$-torsion-free in the sense that $pb = 0$ implies $b = 0$. Let $D$ be a graded Cartier module datum over $(B,j)$, that is, a $W(B)$-module $D.M$ with additive endomorphisms $F$, $V$, a $W(B)$-linear $\Pi$ and two $W(B)$-submodules $D.\mathrm{piece}\,0$, $D.\mathrm{piece}\,1$ subject to the usual Cartier relations ($F$ is $\sigma$-semilinear, $V$ is $\sigma^{-1}$-semilinear, $V(w\cdot Fx) = V(w)\cdot x$, $FV = p$, $\Pi$ commutes with $F$ and $V$, $\Pi^2 = p$), the two pieces being complementary and each of $F$, $V$, $\Pi$ shifting the grading by one. Assume $D$ is special, i.e. it admits a homogeneous $V$-basis ($\gamma_i \in D.\mathrm{piece}\,i$ such that every $x$ is uniquely $\sum_i \tau(c_i)\gamma_i + V y$ with $c_i \in B$, $\tau$ the Teichmüller lift) and is $V$-adically complete (every sequence $(x_m)$ in $D.M$ has a unique sum $s$ with $s \equiv \sum_{m<N} V^m x_m$ modulo $V^N D.M$ for all $N$). Then there exist: a formal $\mathcal{O}_D$-module $X$ over $B$ (a commutative two-dimensional formal group law $F_X$ with an additive action of $W(\mathbb{F}_{p^2})$ by law endomorphisms and an endomorphism $\varpi$ satisfying $\varpi \circ \varpi = [p]$ and $\varpi \circ [a] = [\sigma a] \circ \varpi$); a proof $hc$ that the degree-$0$ and degree-$1$ graded pieces of the Cartier module $\mathrm{CartierModule}\,p\,X.F$ (the subgroups on which the Teichmüller elements $\tau(c)$, $c \in \mathbb{F}_{p^2}$, act through the homothety by $j(\tau c)^{p^n}$) are complementary; a family $\gamma : \mathrm{Fin}\,2 \to \mathrm{CartierModule}\,p\,X.F$ with $\gamma_i$ in the graded piece of degree $i$ and with invertible tangent determinant $\det(\mathrm{tangent}(\gamma_i)_k)$; and an additive map $g$ from the graded Cartier datum attached to $X$ (underlying module the Cartier module of $X$, with Cartier $F$, the integral Verschiebung, the action of $\varpi$, and the two graded submodules) to $D.M$ which is bijective, $W(B)$-linear, commutes with $F$, with $V$ and with $\Pi$, and sends the piece of degree $i$ into $D.\mathrm{piece}\,i$. Compatibility with the grading is asserted only as this inclusion, not as an equality of pieces.
--
--   This is the realisation half of the classification of special formal $\mathcal{O}_D$-modules by their graded Cartier data: over a $p$-torsion-free base every abstract special datum is isomorphic to the datum of an actual formal $\mathcal{O}_D$-module law. It is used to replace abstract torsion-free data by concrete model laws, in particular in the construction of base-changed special data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_exists_formalODModule_bijective_of_isSpecialCartierModule_of_torsionFree.lean

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
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.GradedCartierModuleData.exists_formalODModule_bijective_of_isSpecialCartierModule_of_torsionFree
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (hB : ∀ b : B, (p : B) * b = 0 → b = 0)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule) :
    ∃ (X : CerednikDrinfeld.FormalODModule p B) (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
      (γ : Fin 2 → MvFormalGroup.CartierModule p X.F) (_ : X.IsHomogeneousVBasis j γ)
      (g : (X.toGradedCartierModuleData j hc).M →+ D.M),
      Function.Bijective g ∧
      (∀ (w : WittVector p B) (x : (X.toGradedCartierModuleData j hc).M), g (w • x) = w • g x) ∧
      (∀ x, g ((X.toGradedCartierModuleData j hc).frobenius x) = D.frobenius (g x)) ∧
      (∀ x, g ((X.toGradedCartierModuleData j hc).verschiebung x) = D.verschiebung (g x)) ∧
      (∀ x, g ((X.toGradedCartierModuleData j hc).varpi x) = D.varpi (g x)) ∧
      (∀ (i : Fin 2) (x : (X.toGradedCartierModuleData j hc).M), x ∈ (X.toGradedCartierModuleData j hc).piece i → g x ∈ D.piece i) := by sorry
