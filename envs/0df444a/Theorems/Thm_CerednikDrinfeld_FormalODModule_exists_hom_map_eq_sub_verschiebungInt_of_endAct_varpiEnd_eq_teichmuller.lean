-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_sub_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller
-- name    : CerednikDrinfeld.FormalODModule.exists_hom_map_eq_sub_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/0857a267-06a7-5584-904c-199bb5e55df1
-- title:
--   Explicit homomorphism of special formal modules from Witt edge relations
-- statement:
--   Fix a prime $p$ and a commutative ring $R$ of characteristic $p$, together with a ring homomorphism $j$ from $\mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2})$ to $R$, and elements $\xi,\eta \in R$ with $\xi\eta = 0$. Let $Y$ and $X$ be formal $\mathcal{O}_D$-modules over $R$, that is, two-dimensional commutative formal group laws equipped with an action of $\mathbb{Z}_{p^2}$ by endomorphisms of the law and an endomorphism $\varpi$ satisfying $\varpi \circ \varpi = [p]$ and $\varpi \circ [a] = [\sigma a] \circ \varpi$ for the Witt Frobenius $\sigma$. Assume both are special with respect to $j$: the Lie module is the direct sum of the submodule where $\mathbb{Z}_{p^2}$ acts through $j$ and the submodule where it acts through $j \circ \sigma$, each of these being an invertible $R$-module. Let $\delta = (\delta_0,\delta_1)$ and $\gamma = (\gamma_0,\gamma_1)$ be homogeneous $V$-bases of the Cartier modules of $Y$ and of $X$ relative to $j$, meaning that $\delta_i$ and $\gamma_i$ lie in the $i$-th graded piece (on which the Teichmüller representative $[c]$, $c \in \mathbb{F}_{p^2}$, acts as the homothety by $j([c])^{p^i}$) and that the $2\times 2$ tangent matrices have unit determinant. Suppose, with $V$ the integral Verschiebung and $\bullet$ the $W(R)$-action on Cartier modules, that $\varpi$ acts by $\varpi\delta_0 = V\delta_0$, $\varpi\delta_1 = V\delta_1$, while $\varpi\gamma_0 = ([\eta^p]-[\eta])\gamma_1 + V\gamma_0$ and $\varpi\gamma_1 = ([\xi^p]-[\xi])\gamma_0 + V\gamma_1$. Then there exists a homomorphism $\rho \colon Y \to X$ of formal $\mathcal{O}_D$-modules (a homomorphism of formal group laws commuting with the $\mathbb{Z}_{p^2}$-action and with $\varpi$) whose induced map on Cartier modules satisfies $\rho(\delta_0) = p\gamma_0 - V([\eta^{p^2}]\gamma_1)$ and $\rho(\delta_1) = p\gamma_1 - V([\xi^{p^2}]\gamma_0)$. No uniqueness is asserted.
--
--   This is the construction, in Cartier-module terms, of the explicit homomorphism along an edge of Drinfeld's family of special formal $\mathcal{O}_D$-modules, the analytic input to the Čerednik–Drinfeld uniformisation of Shimura curves. It is the existence half of the edge statement that combines it with the computation of the structure constants and with the assertion that the resulting map is an isogeny of height $4$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_sub_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.lean

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

theorem CerednikDrinfeld.FormalODModule.exists_hom_map_eq_sub_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller
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
    ∃ ρ : FormalODModule.Hom Y X,
      CartierModule.map ρ.toLawHom (δ 0) =
          (p : WittVector p R) • γ 0 - verschiebungInt (WittVector.teichmuller p (η ^ p ^ 2) • γ 1) ∧
      CartierModule.map ρ.toLawHom (δ 1) =
          (p : WittVector p R) • γ 1 - verschiebungInt (WittVector.teichmuller p (ξ ^ p ^ 2) • γ 0) := by sorry
