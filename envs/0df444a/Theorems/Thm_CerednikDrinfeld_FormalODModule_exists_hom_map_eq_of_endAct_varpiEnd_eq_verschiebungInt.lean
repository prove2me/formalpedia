-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_of_endAct_varpiEnd_eq_verschiebungInt
-- name    : CerednikDrinfeld.FormalODModule.exists_hom_map_eq_of_endAct_varpiEnd_eq_verschiebungInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/5233b7e5-754c-5820-8ca7-bf35ccdbe9ff
-- title:
--   Transporting homogeneous V-bases with Pi = V
-- statement:
--   Let $p$ be a prime, let $R$ be a commutative ring of characteristic $p$, and let $j \colon \mathbb{Z}_{p^2} \to R$ be a ring homomorphism, where $\mathbb{Z}_{p^2}$ denotes the Witt vectors of $\mathbb{F}_{p^2}$. Let $Y$ and $X$ be formal $\mathcal{O}_D$-modules over $R$, that is, commutative two-dimensional formal group laws $Y.F$, $X.F$ together with an additive and multiplicative action of $\mathbb{Z}_{p^2}$ by endomorphisms and a further endomorphism $\varpi$ satisfying $\varpi \circ \varpi = [p]$ and $\varpi \circ [a] = [\sigma(a)] \circ \varpi$ for the Frobenius $\sigma$ of $\mathbb{Z}_{p^2}$. Suppose $\delta_0, \delta_1$ in the Cartier module of $Y.F$ form a homogeneous $V$-basis relative to $j$, meaning that $\delta_i$ lies in the $i$-th graded piece (for each $c \in \mathbb{F}_{p^2}$, the Teichmüller lift of $c$ acts on $\delta_i$ as the homothety by $j(\tau(c))^{p^i}$) and that the determinant of the $2 \times 2$ matrix of tangent coefficients of $\delta_0, \delta_1$ is a unit in $R$; suppose likewise for $\gamma_0, \gamma_1$ in the Cartier module of $X.F$. Assume moreover that the endomorphism induced by $Y.\varpi$ sends each $\delta_i$ to $\mathrm{verschiebungInt}(\delta_i)$, and that the endomorphism induced by $X.\varpi$ sends each $\gamma_i$ to $\mathrm{verschiebungInt}(\gamma_i)$. Then there exists a homomorphism $\iota \colon Y \to X$ of formal $\mathcal{O}_D$-modules (a homomorphism of formal group laws commuting with the $\mathbb{Z}_{p^2}$-action and with $\varpi$) whose induced map on Cartier modules carries $\delta_0$ to $\gamma_0$ and $\delta_1$ to $\gamma_1$.
--
--   This is the transport statement for node-type formal $\mathcal{O}_D$-modules in the Čerednik–Drinfeld part of the development: two such modules whose $\varpi$ acts as the Verschiebung on a homogeneous $V$-basis are linked by an $\mathcal{O}_D$-homomorphism matching the bases, and applying it in both directions yields an isomorphism. It is used in the analysis of the edge isogeny, namely in the construction of Cartier quadruples along an edge and in the computation that the edge isogeny has height four.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_of_endAct_varpiEnd_eq_verschiebungInt.lean

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

theorem CerednikDrinfeld.FormalODModule.exists_hom_map_eq_of_endAct_varpiEnd_eq_verschiebungInt
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [CharP R p] (j : Zp2 p →+* R)
    (Y X : FormalODModule p R)
    (δ : Fin 2 → CartierModule p Y.F) (hδ : Y.IsHomogeneousVBasis j δ)
    (hδ0 : endAct Y.varpiEnd (δ 0) = verschiebungInt (δ 0)) (hδ1 : endAct Y.varpiEnd (δ 1) = verschiebungInt (δ 1))
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hγ0 : endAct X.varpiEnd (γ 0) = verschiebungInt (γ 0)) (hγ1 : endAct X.varpiEnd (γ 1) = verschiebungInt (γ 1)) :
    ∃ ι : FormalODModule.Hom Y X,
      CartierModule.map ι.toLawHom (δ 0) = γ 0 ∧ CartierModule.map ι.toLawHom (δ 1) = γ 1 := by sorry
