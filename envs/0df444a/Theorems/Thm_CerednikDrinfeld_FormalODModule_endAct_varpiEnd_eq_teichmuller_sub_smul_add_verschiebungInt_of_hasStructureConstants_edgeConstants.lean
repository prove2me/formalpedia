-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_endAct_varpiEnd_eq_teichmuller_sub_smul_add_verschiebungInt_of_hasStructureConstants_edgeConstants
-- name    : CerednikDrinfeld.FormalODModule.endAct_varpiEnd_eq_teichmuller_sub_smul_add_verschiebungInt_of_hasStructureConstants_edgeConstants
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/a6d7d428-6e78-5a0c-8098-bf4664019e4c
-- title:
--   Closed Witt form of the edge structure constants
-- statement:
--   Let $p$ be a prime and $R$ a commutative ring of characteristic $p$, equipped with a ring homomorphism $j\colon W(\mathbb F_{p^2})\to R$, and let $\xi,\eta\in R$ satisfy $\xi\eta=0$. Let $X$ be a formal $\mathcal O_D$-module over $R$, that is, a commutative $2$-dimensional formal group law $F=X.F$ together with a family of endomorphisms $\mathrm{act}(a)$ for $a\in W(\mathbb F_{p^2})$, which is multiplicative, additive and unital, and a law endomorphism $\varpi$ with $\varpi\circ\varpi=\mathrm{act}(p)$ and $\varpi\circ\mathrm{act}(a)=\mathrm{act}(\mathrm{Frob}\,a)\circ\varpi$; write $\Pi=\mathrm{endAct}\,X.\mathrm{varpiEnd}$ for the induced additive endomorphism of the Cartier module $\mathrm{CartierModule}\,p\,F$ and $V=\mathrm{verschiebungInt}$. Let $\gamma\colon\{0,1\}\to\mathrm{CartierModule}\,p\,F$ be a homogeneous $V$-basis with respect to $j$: each $\gamma_i$ lies in the $i$-th graded piece, i.e. $\mathrm{endAct}(X.\mathrm{actEnd}([c]))\gamma_i=j([c])^{p^i}\gamma_i$ for every $c\in\mathbb F_{p^2}$ (homothety by $j([c])^{p^i}$), and the matrix $(\mathrm{tangent}(\gamma_i)_k)_{i,k}$ has unit determinant. Assume further that $\gamma$ has structure constants given by the edge family: for each $i$ and each $N$ there is $h$ with $\Pi\gamma_i=\sum_{m<N}V^m\bigl(a_{m,i}\cdot\gamma_{(m+i+1)\bmod 2}\bigr)+V^N h$, where $a_{m,0}$ and $a_{m,1}$ are the branch constants of $\eta$ and of $\xi$ respectively, namely $x^p-x$ for $m=0$, $1$ for $m=1$, the $(m/2)$-th Witt digit of $x$ raised to the power $p^{m/2}$ for even $m\ge 2$, and $0$ for odd $m\ge 3$. Then both closed identities hold exactly: $\Pi\gamma_0=\bigl([\eta^p]-[\eta]\bigr)\cdot\gamma_1+V\gamma_0$ and $\Pi\gamma_1=\bigl([\xi^p]-[\xi]\bigr)\cdot\gamma_0+V\gamma_1$, where $[\,\cdot\,]$ denotes the Teichmüller representative in $W(R)$ acting on the Cartier module.
--
--   This converts the asymptotic, digit-by-digit description of the action of the uniformiser $\Pi$ on a homogeneous $V$-basis of the Cartier module of a special formal $\mathcal O_D$-module into the closed Witt-vector relations used in Drinfeld's description of the formal moduli along an edge of the tree, the parameters $\xi,\eta$ with $\xi\eta=0$ being the edge coordinates (the node fibre corresponding to $\xi=\eta=0$, where $\Pi\gamma_i=V\gamma_i$). It is the input to the subsequent construction of a normalised basis of the Cartier module and of the height-one isogeny attached to $\Pi-V$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_endAct_varpiEnd_eq_teichmuller_sub_smul_add_verschiebungInt_of_hasStructureConstants_edgeConstants.lean

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
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule

theorem CerednikDrinfeld.FormalODModule.endAct_varpiEnd_eq_teichmuller_sub_smul_add_verschiebungInt_of_hasStructureConstants_edgeConstants
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [CharP R p] (j : Zp2 p →+* R)
    (ξ η : R) (hξη : ξ * η = 0)
    (X : FormalODModule p R) (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (ha : X.HasStructureConstants γ (EdgeFamily.edgeConstants p ξ η)) :
    endAct X.varpiEnd (γ 0) =
        (WittVector.teichmuller p (η ^ p) - WittVector.teichmuller p η) • γ 1 + verschiebungInt (γ 0) ∧
      endAct X.varpiEnd (γ 1) =
        (WittVector.teichmuller p (ξ ^ p) - WittVector.teichmuller p ξ) • γ 0 + verschiebungInt (γ 1) := by sorry
