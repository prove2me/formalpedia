-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp
-- name    : CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/d878e7c0-8471-54f2-bba0-704edc82c8fb
-- title:
--   Kernel degrees multiply under composition of series
-- statement:
--   Let $B$ be a commutative Noetherian ring, and let $\varphi,\psi$ be elements of `Series B`, that is, pairs $(\varphi_0,\varphi_1)$, $(\psi_0,\psi_1)$ of formal power series in two variables over $B$ (functions $\mathrm{Fin}\,2 \to B[[x_0,x_1]]$), and let $d,e$ be natural numbers. Assume every component of $\varphi$ and every component of $\psi$ has vanishing constant coefficient, and that `HasKernelOfDegree` holds for $\varphi$ with $d$ and for $\psi$ with $e$: for $\varphi$ this means that the quotient $\mathrm{KerAlgebra}\,\varphi = B[[x_0,x_1]]/(\varphi_0,\varphi_1)$ is finite as a $B$-module, projective as a $B$-module, and that for every field $\kappa$ (in the same universe) and every ring homomorphism $f : B \to \kappa$ the $\kappa$-vector space $\kappa[[x_0,x_1]]/(f(\varphi_0),f(\varphi_1))$ has dimension exactly $d$, where $f$ is applied coefficientwise; likewise for $\psi$ with $e$. The conclusion is that the composite `ψ.comp φ`, whose $i$-th component is the substitution $\psi_i(\varphi_0,\varphi_1)$, satisfies `HasKernelOfDegree` with the number $d \cdot e$: the quotient $B[[x_0,x_1]]/(\psi_0(\varphi),\psi_1(\varphi))$ is a finite projective $B$-module, and its fibre dimension at every field-valued point of $B$ equals $d\,e$.
--
--   This is the multiplicativity of the degree of the kernel of a composite of two two-variable substitution maps, the formal-scheme counterpart of the multiplicativity of degrees of isogenies. It is used throughout the treatment of special formal $\mathcal{O}_D$-modules, for instance in computing the kernel degrees of powers of the $\mathbb{Z}_p$-action and of $\varpi$, and in the rigidity statements that compare composites with powers of the action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp
    {B : Type} [CommRing B] [IsNoetherianRing B] {φ ψ : Series B} {d e : ℕ}
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (hψ0 : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0)
    (hφ : FormalODModule.HasKernelOfDegree φ d) (hψ : FormalODModule.HasKernelOfDegree ψ e) :
    FormalODModule.HasKernelOfDegree (ψ.comp φ) (d * e) := by sorry
