-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_of_comp
-- name    : CerednikDrinfeld.FormalODModule.HasKernelOfDegree.of_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/9de6e80c-06e5-5685-b23a-c8bb0fde6710
-- title:
--   Cancelling a finite locally free kernel of degree d
-- statement:
--   Let $B$ be a commutative Noetherian ring and let $\varphi,\psi$ be pairs of formal power series in two variables over $B$, i.e. elements of $\mathrm{Series}\,B = \mathrm{Fin}\,2 \to B[\![x_0,x_1]\!]$, and let $d,e$ be natural numbers. Assume every component of $\varphi$ and every component of $\psi$ has vanishing constant coefficient. Assume further that $\varphi$ has kernel of degree $d$ and that the composite $\psi\circ\varphi$, whose $i$-th component is $\psi_i(\varphi_0,\varphi_1)$ (substitution of $\varphi$ into $\psi_i$), has kernel of degree $d\cdot e$, where "$\chi$ has kernel of degree $n$" means: the quotient $B[\![x_0,x_1]\!]/(\chi_0,\chi_1)$ is a finite and projective $B$-module, and for every field $\kappa$ and every ring homomorphism $f : B \to \kappa$ the $\kappa$-vector space $\kappa[\![x_0,x_1]\!]/(f_*\chi_0, f_*\chi_1)$ has dimension $n$. The conclusion is that $\psi$ has kernel of degree $e$ in the same sense.
--
--   This is the cancellation (division) property for degrees of finite locally free kernels, converse to the multiplicativity of degrees under composition, formulated for the kernel algebras of pairs of power series that arise as homomorphisms of two-dimensional formal groups in the Čerednik–Drinfeld special formal module material. It is used in the statements [`CerednikDrinfeld.FormalODModule.HasKernelOfDegree.le_and_of_comp_pow`](thm.html#CerednikDrinfeld.FormalODModule.HasKernelOfDegree.le_and_of_comp_pow) and [`CerednikDrinfeld.FormalODModule.hasHeight_four_of_isIsogenyOfHeight`](thm.html#CerednikDrinfeld.FormalODModule.hasHeight_four_of_isIsogenyOfHeight).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_of_comp.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.HasKernelOfDegree.of_comp
    {B : Type} [CommRing B] [IsNoetherianRing B] {φ ψ : Series B} {d e : ℕ}
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (hψ0 : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0)
    (hφ : FormalODModule.HasKernelOfDegree φ d) (hcomp : FormalODModule.HasKernelOfDegree (ψ.comp φ) (d * e)) :
    FormalODModule.HasKernelOfDegree ψ e := by sorry
