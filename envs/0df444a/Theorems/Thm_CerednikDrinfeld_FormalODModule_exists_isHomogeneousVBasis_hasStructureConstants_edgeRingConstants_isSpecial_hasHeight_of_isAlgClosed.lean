-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_hasStructureConstants_edgeRingConstants_isSpecial_hasHeight_of_isAlgClosed
-- name    : CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_hasStructureConstants_edgeRingConstants_isSpecial_hasHeight_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/2cc1b753-bc71-5c02-9b92-225dc69135cd
-- title:
--   Special formal mathcal O_D-module of height 4 over the edge chart
-- statement:
--   Let $p$ be a prime and $k$ an algebraically closed field of characteristic $p$, and let $\iota \colon \mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2}) \to W(k)$ be a ring homomorphism (here `Zp2 p` is the Witt ring of `GaloisField p 2`). Put $\bar{A} = W(k)/(p)$ and let $B =$ `EdgeFamily.edgeRingCharP p` $\bar{A}$, the localisation away from the element `edgeQuot.discr` $\bar{A}\,0\,p$ of the corresponding edge quotient ring, and let $j \colon \mathbb{Z}_{p^2} \to B$ be $\iota$ followed by the quotient map $W(k) \to \bar{A}$ and the structure map $\bar{A} \to B$. The assertion is that there exist a formal $\mathcal{O}_D$-module $X$ over $B$ — a commutative two-dimensional formal group law $X.F$ over $B$ with an action of $\mathbb{Z}_{p^2}$ by law endomorphisms and an endomorphism $\varpi$ satisfying $\varpi \circ \varpi = [p]$ and $\varpi \circ a = \sigma(a) \circ \varpi$ — and a pair $\gamma_0, \gamma_1$ of elements of the Cartier module of $X.F$ such that: (i) each $\gamma_i$ lies in the graded piece of index $i$ for $j$, i.e. $\mathrm{End}(a(\omega(c)))\gamma_i = \langle j(\omega(c))^{p^i}\rangle \gamma_i$ for all $c \in \mathbb{F}_{p^2}$ ($\omega$ the Teichmüller lift), and the $2 \times 2$ matrix of tangent coordinates of the $\gamma_i$ has unit determinant; (ii) $\gamma$ has structure constants the edge constants $a_{m,0} =$ `branchConstants p η m`, $a_{m,1} =$ `branchConstants p ξ m` for the two chart parameters $\xi, \eta$ of $B$, meaning that for each $i$ and each $N$ one has $\varpi_* \gamma_i = \sum_{m<N} V^m \langle a_{m,i}\rangle \gamma_{(m+i+1) \bmod 2} + V^N h$ for some Cartier module element $h$, with $V$ the integral Verschiebung; (iii) $X$ is special for $j$: the submodules `lieZero` and `lieOne` of the Lie module of $X$ are complementary and each is an invertible $B$-module; (iv) $X$ has height $4$, i.e. the kernel algebra of the series $X.\mathrm{act}(p)$ is a finite projective $B$-module whose fibre over every field-valued point of $B$ has dimension $p^4$.
--
--   This is Drinfeld's explicit edge family: over the reduced standard edge chart of the formal upper half-plane it produces a special formal $\mathcal{O}_D$-module of height $4$ with prescribed structure constants. It feeds the construction of admissible rigidified Cartier quadruples whose line invariant realises the edge chart, the step towards local surjectivity in the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_hasStructureConstants_edgeRingConstants_isSpecial_hasHeight_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

universe u

theorem CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_hasStructureConstants_edgeRingConstants_isSpecial_hasHeight_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k) :
    ∃ (X : FormalODModule p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (γ : Fin 2 → CartierModule p X.F),
      X.IsHomogeneousVBasis (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) γ ∧
      X.HasStructureConstants γ (EdgeFamily.edgeRingConstants p (WittVector p k ⧸ pIdeal p (WittVector p k))) ∧
      X.IsSpecial (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) ∧ X.HasHeight 4 := by sorry
