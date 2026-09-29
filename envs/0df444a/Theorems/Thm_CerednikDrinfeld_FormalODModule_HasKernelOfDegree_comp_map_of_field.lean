-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_map_of_field
-- name    : CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp_map_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/6522c760-f8e3-5a0c-a997-315b7802870d
-- title:
--   Multiplicativity of kernel degrees under composition with a series over a field
-- statement:
--   Let $R$ be a commutative ring and $\kappa$ a field, both in the same universe, and let $f \colon \kappa \to R$ be a ring homomorphism. Let $\psi = (\psi_0,\psi_1)$ be a pair of power series in two variables over $R$ and $a$ a natural number such that `FormalODModule.HasKernelOfDegree` holds for $\psi$ with degree $a$, that is: the quotient $R[[X_0,X_1]]/(\psi_0,\psi_1)$ is a finite projective $R$-module and, for every field $\kappa'$ in the ambient universe and every ring homomorphism $g \colon R \to \kappa'$, the $\kappa'$-algebra $\kappa'[[X_0,X_1]]/(\psi_0^g,\psi_1^g)$ obtained by applying $g$ to all coefficients has $\operatorname{finrank}_{\kappa'}$ equal to $a$. Let $\varphi = (\varphi_0,\varphi_1)$ be a pair of power series in two variables over $\kappa$, each with vanishing constant coefficient, and $b$ a natural number such that the same predicate holds for $\varphi$ with degree $b$. Then the predicate holds with degree $a\,b$ for the composite $\psi \circ \varphi^f$, whose $i$-th component is obtained by substituting the coefficientwise image $\varphi^f = (\,\mathrm{map}\,f\,\varphi_0, \mathrm{map}\,f\,\varphi_1)$ into $\psi_i$: the quotient $R[[X_0,X_1]]/\bigl(\psi_0(\varphi^f),\psi_1(\varphi^f)\bigr)$ is finite and projective over $R$, and all its specialisations to fields have dimension $a\,b$.
--
--   This is the multiplicativity of the degree (height) of isogenies of two-dimensional formal groups in the special case where the inner isogeny is defined over a field and transported to $R$ along $f$, stated for the project's notion of a pair of series having a finite locally free kernel algebra of prescribed degree. It is used to compose kernel-degree data in the Čerednik–Drinfel'd setting, and is cited by the corresponding composition, divisibility and cancellation lemmas for `HasKernelOfDegree`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_map_of_field.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp_map_of_field
    {R : Type u} [CommRing R] {κ : Type u} [Field κ] (f : κ →+* R)
    {ψ : Series R} {a : ℕ} (hψ : FormalODModule.HasKernelOfDegree ψ a)
    {φ : Series κ} {b : ℕ} (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφ : FormalODModule.HasKernelOfDegree φ b) :
    FormalODModule.HasKernelOfDegree (ψ.comp (φ.map f)) (a * b) := by sorry
