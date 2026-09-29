-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_nMap_bijOn_eta_of_eq_baseChangeEq_mk
-- name    : CerednikDrinfeld.FormalODModule.nMap_bijOn_eta_of_eq_baseChangeEq_mk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/a652c35c-5b9d-5556-9b87-3a929a717b89
-- title:
--   Reduction mod p is bijective on η-invariants
-- statement:
--   Fix a prime $p$ and a commutative ring $S$ in which $p$ is nilpotent, together with a ring homomorphism $j : W(\mathbf{F}_{p^2}) \to S$ and a formal $\mathcal{O}_D$-module $X$ over $S$ (a two-dimensional formal group law $X.F$ with commutativity, an additive action of $W(\mathbf{F}_{p^2})$ and a uniformiser endomorphism $\varpi$ satisfying $\varpi^2 = [p]$ and $\varpi \circ [a] = [\sigma a] \circ \varpi$). Assume: a family $\gamma : \mathrm{Fin}\,2 \to$ `CartierModule p X.F` with $\gamma_i$ in the $i$-th graded piece for $j$ (the elements on which each Teichmüller lift $\tau(c)$, $c \in \mathbf{F}_{p^2}$, acts by the homothety $j(\tau(c))^{p^i}$) and with the determinant of the matrix of tangent coordinates $(\mathrm{tangent}(\gamma_i)_k)$ a unit; that the graded pieces for $n = 0,1$ are complementary, both for $X$ over $S$ and for a formal $\mathcal{O}_D$-module $Xb$ over $S/pS$ with $Xb$ the base change of $X$ along `Ideal.Quotient.mk (pIdeal p S)`, $jb$ the composite of $j$ with that quotient map, and $Xb.F$ the reduction of $X.F$; an additive map $red$ between the Cartier modules equal to the base change `CartierModule.baseChangeEq` along the quotient map, commuting with the Verschiebung and with $\varpi$ of the associated graded Cartier module data; and canonical $L$-maps $L$ for $X$ and $Lb$ for $Xb$ satisfying $Lb \circ red = N(red) \circ L$, where $N(red)$ is the map `nMap` induced by $red$ on the quotients $N(M)$. Then $N(red)$ maps the subgroup $\eta(L)$ (the fixed points of the endomorphism `phi` attached to $L$) bijectively onto $\eta(Lb)$.
--
--   This is the assertion that passage to the reduction modulo $p$ induces a bijection on the $\varphi$-invariants $\eta$ of the $N$-module of the Cartier module of a formal $\mathcal{O}_D$-module over a $p$-nilpotent base, as in Boutot–Carayol's treatment of the Čerednik–Drinfeld uniformisation. It is used in the analysis of rigidified formal $\mathcal{O}_D$-modules, where $\eta$ supplies the lattice-theoretic coordinates attached to a rigidification.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_nMap_bijOn_eta_of_eq_baseChangeEq_mk.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega
  MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

universe u

theorem CerednikDrinfeld.FormalODModule.nMap_bijOn_eta_of_eq_baseChangeEq_mk
    (p : ℕ) [Fact p.Prime] {S : Type} [CommRing S] (hS : IsNilpotent (p : S))
    (j : Zp2 p →+* S) (X : FormalODModule p S)
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (Xb : FormalODModule p (S ⧸ pIdeal p S)) (hXb : X.map (Ideal.Quotient.mk (pIdeal p S)) = Xb)
    (jb : Zp2 p →+* S ⧸ pIdeal p S) (hjb : (Ideal.Quotient.mk (pIdeal p S)).comp j = jb)
    (hcb : IsCompl (Xb.gradedPiece jb 0) (Xb.gradedPiece jb 1))
    (hF : X.F.map (Ideal.Quotient.mk (pIdeal p S)) = Xb.F)
    (red : CartierModule p X.F →+ CartierModule p Xb.F)
    (hred : red = CartierModule.baseChangeEq (Ideal.Quotient.mk (pIdeal p S)) hF)
    (hredV : ∀ x, red ((X.toGradedCartierModuleData j hc).verschiebung x) =
      (Xb.toGradedCartierModuleData jb hcb).verschiebung (red x))
    (hredPi : ∀ x, red ((X.toGradedCartierModuleData j hc).varpi x) =
      (Xb.toGradedCartierModuleData jb hcb).varpi (red x))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (Lb : (Xb.toGradedCartierModuleData jb hcb).M →+ (Xb.toGradedCartierModuleData jb hcb).NMod)
    (hLb : (Xb.toGradedCartierModuleData jb hcb).IsCanonicalLMap Lb)
    (hLL : ∀ x, Lb (red x) =
      (X.toGradedCartierModuleData j hc).nMap (Xb.toGradedCartierModuleData jb hcb) red hredV hredPi (L x)) :
    Set.BijOn ((X.toGradedCartierModuleData j hc).nMap (Xb.toGradedCartierModuleData jb hcb) red hredV hredPi)
      ((X.toGradedCartierModuleData j hc).eta L hL.isCartierLMap.map_verschiebung : Set _)
      ((Xb.toGradedCartierModuleData jb hcb).eta Lb hLb.isCartierLMap.map_verschiebung : Set _) := by sorry
