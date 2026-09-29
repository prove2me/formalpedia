-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller
-- name    : CerednikDrinfeld.FormalODModule.exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/041a7fe1-8781-55a0-8aa4-71f1fe0823fa
-- title:
--   Dual edge homomorphism ρᵈagger: X→ Y on Cartier modules
-- statement:
--   Let $p$ be a prime and $R$ a commutative ring of characteristic $p$, equipped with a ring homomorphism $j\colon \mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2}) \to R$, and let $\xi,\eta \in R$ satisfy $\xi\eta = 0$. Let $Y$ and $X$ be formal $\mathcal{O}_D$-modules over $R$ in the sense of the structure `FormalODModule`: each carries a commutative two-dimensional formal group law over $R$, an action of $\mathbb{Z}_{p^2}$ by endomorphisms of that law, and an endomorphism series $\varpi$ with $\varpi\circ\varpi = [p]$ and $\varpi\circ a = \sigma(a)\circ\varpi$ for all $a$, $\sigma$ the Witt-vector Frobenius. Both are assumed special for $j$, that is, the two submodules of the Lie algebra on which $a$ acts by $j(a)$ and by $j(\sigma a)$ are complementary and invertible. Let $\delta = (\delta_0,\delta_1)$ and $\gamma = (\gamma_0,\gamma_1)$ be homogeneous $V$-bases of the Cartier modules of $Y$ and of $X$ for $j$: $\delta_i$ (resp. $\gamma_i$) lies in the graded piece of degree $i$, on which each Teichmüller element $[c]$, $c \in \mathbb{F}_{p^2}$, acts by the homothety $j([c])^{p^i}$, and the matrix of tangent vectors of the basis has invertible determinant. Assume that $\varpi$ acts on the Cartier module of $Y$ by $\varpi\delta_i = V\delta_i$ for $i = 0,1$, and on that of $X$ by $\varpi\gamma_0 = ([\eta^p]-[\eta])\gamma_1 + V\gamma_0$ and $\varpi\gamma_1 = ([\xi^p]-[\xi])\gamma_0 + V\gamma_1$, the scalars being differences of Teichmüller representatives in $W(R)$ and $V$ the integral Verschiebung. Then there exists a homomorphism $\rho$ of formal $\mathcal{O}_D$-modules from $X$ to $Y$ (a pair of power series which is a homomorphism of formal group laws and commutes with the $\mathbb{Z}_{p^2}$-action and with $\varpi$) whose induced additive map on Cartier modules satisfies $\rho(\gamma_0) = p\,\delta_0 + V([\eta^{p^2}]\delta_1)$ and $\rho(\gamma_1) = p\,\delta_1 + V([\xi^{p^2}]\delta_0)$.
--
--   This produces the dual $\rho^\dagger$ of the edge isogeny in the Čerednik–Drinfeld description of special formal $\mathcal{O}_D$-modules, constructed at the level of Cartier modules from the prescribed $\varpi$-structure constants of the two bases. It is used in the construction of Cartier quadruples along an edge and in the verification that the edge isogeny has height four.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.lean

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

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule

theorem CerednikDrinfeld.FormalODModule.exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [CharP R p] (j : Zp2 p →+* R)
    (ξ η : R) (hξη : ξ * η = 0)
    (Y X : FormalODModule p R) (hYs : Y.IsSpecial j) (hXs : X.IsSpecial j)
    (δ : Fin 2 → CartierModule p Y.F) (hδ : Y.IsHomogeneousVBasis j δ)
    (hδ0 : endAct Y.varpiEnd (δ 0) = verschiebungInt (δ 0))
    (hδ1 : endAct Y.varpiEnd (δ 1) = verschiebungInt (δ 1))
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hγ0 : endAct X.varpiEnd (γ 0) =
      (WittVector.teichmuller p (η ^ p) - WittVector.teichmuller p η) • γ 1 + verschiebungInt (γ 0))
    (hγ1 : endAct X.varpiEnd (γ 1) =
      (WittVector.teichmuller p (ξ ^ p) - WittVector.teichmuller p ξ) • γ 0 + verschiebungInt (γ 1)) :
    ∃ ρ : FormalODModule.Hom X Y,
      CartierModule.map ρ.toLawHom (γ 0) =
          (p : WittVector p R) • δ 0 + verschiebungInt (WittVector.teichmuller p (η ^ p ^ 2) • δ 1) ∧
      CartierModule.map ρ.toLawHom (γ 1) =
          (p : WittVector p R) • δ 1 + verschiebungInt (WittVector.teichmuller p (ξ ^ p ^ 2) • δ 0) := by sorry
