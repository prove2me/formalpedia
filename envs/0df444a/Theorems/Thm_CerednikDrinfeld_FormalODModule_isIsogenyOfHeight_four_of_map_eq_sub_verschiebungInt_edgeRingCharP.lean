-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_isIsogenyOfHeight_four_of_map_eq_sub_verschiebungInt_edgeRingCharP
-- name    : CerednikDrinfeld.FormalODModule.isIsogenyOfHeight_four_of_map_eq_sub_verschiebungInt_edgeRingCharP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/f8979276-d146-5496-9788-78d6e6089318
-- title:
--   Explicit edge homomorphism is an isogeny of height 4
-- statement:
--   Let $p$ be a prime, $k$ a field of characteristic $p$, and $B =$ `EdgeFamily.edgeRingCharP p k`, the localisation of the standard edge quotient ring of $k$ away from its discriminant, with distinguished elements $\xi,\eta \in B$; let $j\colon W(\mathbb F_{p^2}) \to B$ be a ring homomorphism. Let $Y$ and $X$ be formal $\mathcal O_D$-modules over $B$, that is, commutative two-dimensional formal group laws equipped with a $W(\mathbb F_{p^2})$-action by law endomorphisms and a law endomorphism $\varpi$ with $\varpi \circ \varpi = [p]$ and $\varpi \circ [a] = [\mathrm{Frob}\,a] \circ \varpi$. Assume each of $Y$, $X$ is special for $j$ (the two eigen-submodules `lieZero j` and `lieOne j` of the Lie module are complementary and invertible) and of height $4$ (the kernel algebra of $[p]$ is finite projective over $B$ of fibre dimension $p^4$ at every field-valued point). Let $\delta$ be a homogeneous $V$-basis of the Cartier module of $Y$ (each $\delta_i$ lies in the $i$-th graded piece for $j$ and the tangent matrix has unit determinant) with $\varpi\delta_i = V\delta_i$ for $i = 0,1$, and $\gamma$ a homogeneous $V$-basis for $X$ with $\varpi\gamma_0 = ([\eta^p]-[\eta])\gamma_1 + V\gamma_0$ and $\varpi\gamma_1 = ([\xi^p]-[\xi])\gamma_0 + V\gamma_1$, Teichmüller lifts being taken in $W(B)$. Let $\rho\colon Y \to X$ be a homomorphism of formal $\mathcal O_D$-modules whose induced map on Cartier modules satisfies $M(\rho)(\delta_0) = p\gamma_0 - V([\eta^{p^2}]\gamma_1)$ and $M(\rho)(\delta_1) = p\gamma_1 - V([\xi^{p^2}]\gamma_0)$. Then $\rho$ is an isogeny of height $4$ from $Y$ to $X$: its defining series is a homomorphism of formal $\mathcal O_D$-modules and the quotient $B[[X_1,X_2]]/(\rho_1,\rho_2)$ is a finite projective $B$-module whose base change along every homomorphism from $B$ to a field has dimension $p^4$.
--
--   This is the height computation for the explicit homomorphism between the two special formal $\mathcal O_D$-modules attached to an edge of the Bruhat–Tits tree in the Čerednik–Drinfeld uniformisation, the structure constants being those of the reduced edge chart with $\xi\eta = 0$. It is used, together with the existence statement for $\rho$, in [`CerednikDrinfeld.FormalODModule.exists_hom_map_eq_sub_verschiebungInt_and_isIsogenyOfHeight_of_hasStructureConstants_edgeConstants`](thm.html#CerednikDrinfeld.FormalODModule.exists_hom_map_eq_sub_verschiebungInt_and_isIsogenyOfHeight_of_hasStructureConstants_edgeConstants).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_isIsogenyOfHeight_four_of_map_eq_sub_verschiebungInt_edgeRingCharP.lean

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

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalODModule.isIsogenyOfHeight_four_of_map_eq_sub_verschiebungInt_edgeRingCharP
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (j : Zp2 p →+* EdgeFamily.edgeRingCharP p k)
    (Y X : FormalODModule p (EdgeFamily.edgeRingCharP p k))
    (hYs : Y.IsSpecial j) (hY4 : Y.HasHeight 4) (hXs : X.IsSpecial j) (hX4 : X.HasHeight 4)
    (δ : Fin 2 → CartierModule p Y.F) (hδ : Y.IsHomogeneousVBasis j δ)
    (hδ0 : endAct Y.varpiEnd (δ 0) = verschiebungInt (δ 0))
    (hδ1 : endAct Y.varpiEnd (δ 1) = verschiebungInt (δ 1))
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hγ0 : endAct X.varpiEnd (γ 0) =
      (WittVector.teichmuller p (EdgeFamily.edgeRingCharP.η p k ^ p) - WittVector.teichmuller p (EdgeFamily.edgeRingCharP.η p k)) • γ 1 +
        verschiebungInt (γ 0))
    (hγ1 : endAct X.varpiEnd (γ 1) =
      (WittVector.teichmuller p (EdgeFamily.edgeRingCharP.ξ p k ^ p) - WittVector.teichmuller p (EdgeFamily.edgeRingCharP.ξ p k)) • γ 0 +
        verschiebungInt (γ 1))
    (ρ : FormalODModule.Hom Y X)
    (hρ0 : CartierModule.map ρ.toLawHom (δ 0) =
      (p : WittVector p (EdgeFamily.edgeRingCharP p k)) • γ 0 -
        verschiebungInt (WittVector.teichmuller p (EdgeFamily.edgeRingCharP.η p k ^ p ^ 2) • γ 1))
    (hρ1 : CartierModule.map ρ.toLawHom (δ 1) =
      (p : WittVector p (EdgeFamily.edgeRingCharP p k)) • γ 1 -
        verschiebungInt (WittVector.teichmuller p (EdgeFamily.edgeRingCharP.ξ p k ^ p ^ 2) • γ 0)) :
    Y.IsIsogenyOfHeight X ρ.toSeries 4 := by sorry
