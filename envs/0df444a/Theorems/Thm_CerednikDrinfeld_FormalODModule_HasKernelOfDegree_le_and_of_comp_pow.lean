-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_le_and_of_comp_pow
-- name    : CerednikDrinfeld.FormalODModule.HasKernelOfDegree.le_and_of_comp_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/354020e5-1b17-56e1-a7c9-ccdea168c67f
-- title:
--   Degree of the outer factor of a composite
-- statement:
--   Let $r$ be a prime and let $B$ be a non-trivial Noetherian commutative ring. Let $\varphi,\psi \in$ `Series B`, i.e. each is a pair of power series in two variables over $B$, and assume that all four series have vanishing constant coefficient. Let $d,D$ be natural numbers. Here `FormalODModule.HasKernelOfDegree θ n` asserts three things about a pair $\theta$: the quotient ring $B[[X_0,X_1]]/(\theta_0,\theta_1)$ is a finite $B$-module, it is projective as a $B$-module, and for every field $\kappa$ and every ring homomorphism $f : B \to \kappa$ the $\kappa$-dimension of $\kappa[[X_0,X_1]]/(f\theta_0,f\theta_1)$ equals $n$. Assume that $\varphi$ has kernel of degree $r^{d}$ in this sense, and that the composite `ψ.comp φ`, whose $i$-th component is $\psi_i$ with $\varphi$ substituted for its variables, has kernel of degree $r^{D}$. The conclusion is twofold: $d \le D$, and $\psi$ itself has kernel of degree $r^{\,D-d}$ in the same sense (with $D-d$ the truncated difference of natural numbers).
--
--   This is the cancellation step for degrees of finite locally free kernels of homomorphisms of two-dimensional formal groups, in the case where the degrees involved are powers of a fixed prime: from the degrees of $\varphi$ and of $\psi\circ\varphi$ one recovers the degree of the outer factor $\psi$. It is used in the height and degree bookkeeping for formal $\mathcal{O}_D$-modules and in the rigidification arguments for fake elliptic curves in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_le_and_of_comp_pow.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.HasKernelOfDegree.le_and_of_comp_pow
    {r : ℕ} [Fact r.Prime] {B : Type} [CommRing B] [IsNoetherianRing B] [Nontrivial B] {φ ψ : Series B}
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (hψ0 : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0)
    {d D : ℕ} (hφ : FormalODModule.HasKernelOfDegree φ (r ^ d))
    (hcomp : FormalODModule.HasKernelOfDegree (ψ.comp φ) (r ^ D)) :
    d ≤ D ∧ FormalODModule.HasKernelOfDegree ψ (r ^ (D - d)) := by sorry
