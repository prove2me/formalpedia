-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_eq_zero_of_nsmul_eq_zero_of_mem_eta
-- name    : CerednikDrinfeld.FormalODModule.eq_zero_of_nsmul_eq_zero_of_mem_eta
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/28a0e6b4-7092-5068-904a-510c31b061d4
-- title:
--   Absence of p-torsion in η(L) over Noetherian bases
-- statement:
--   Fix a prime $p$ and a Noetherian commutative ring $S$ (of type `Type`) in which the image of $p$ is nilpotent, together with a ring homomorphism $j : W(\mathbb{F}_{p^2}) \to S$. Let $X$ be a formal $\mathcal{O}_D$-module over $S$, that is, a commutative two-dimensional formal group law $F$ over $S$ equipped with an action of $W(\mathbb{F}_{p^2})$ by endomorphisms of $F$ and an endomorphism $\varpi$ with $\varpi \circ \varpi$ the action of $p$ and $\varpi$ semilinear for the Witt-vector Frobenius. Let $\gamma : \{0,1\} \to$ `CartierModule p X.F` be a homogeneous $V$-basis, meaning that $\gamma_i$ lies in the $i$-th graded piece (the elements on which the action of the Teichmüller lift of each $c \in \mathbb{F}_{p^2}$ agrees with the homothety by $j(\tau(c))^{p^i}$) and the $2 \times 2$ matrix of tangent coefficients of the $\gamma_i$ has unit determinant, and suppose the graded pieces in degrees $0$ and $1$ are complementary subgroups of the Cartier module, so that the latter acquires the structure $D$ of graded Cartier module data over $S$ with respect to $j$. Let $L : D.M \to D.\mathrm{NMod}$ be an additive map which is a canonical $L$-map (a Cartier $L$-map admitting a lift along a surjection from a ring without $p$-torsion carrying a special graded Cartier module datum). Finally let $\zeta \in D.\mathrm{NMod}$ lie in $\eta(L)$, the kernel of $\varphi_L - \mathrm{id}$, and satisfy $p\,\zeta = 0$. Then $\zeta = 0$.
--
--   This is the statement that $\eta(L)$ is free of $p$-torsion, extended from reduced rings of characteristic $p$ to Noetherian bases in which $p$ is nilpotent, as in Boutot–Carayol's analysis of the Cartier-theoretic description of formal $\mathcal{O}_D$-modules. It is used in the rigidified setting, where it supplies the injectivity needed for comparing $\eta$-sections and for producing elements of the $\eta$-piece with prescribed image under base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_eq_zero_of_nsmul_eq_zero_of_mem_eta.lean

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

theorem CerednikDrinfeld.FormalODModule.eq_zero_of_nsmul_eq_zero_of_mem_eta
    (p : ℕ) [Fact p.Prime] {S : Type} [CommRing S] [IsNoetherianRing S] (hS : IsNilpotent (p : S))
    (j : Zp2 p →+* S) (X : FormalODModule p S)
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (ζ : (X.toGradedCartierModuleData j hc).NMod)
    (hζ : ζ ∈ (X.toGradedCartierModuleData j hc).eta L hL.isCartierLMap.map_verschiebung)
    (hp : p • ζ = 0) :
    ζ = 0 := by sorry
