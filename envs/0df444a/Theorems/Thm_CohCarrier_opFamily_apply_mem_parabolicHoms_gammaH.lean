-- Prove2me | Theorems.Thm_CohCarrier_opFamily_apply_mem_parabolicHoms_gammaH
-- name    : CohCarrier.opFamily_apply_mem_parabolicHoms_gammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/1d931600-b233-5e3d-be7b-3efd84f86098
-- title:
--   Hecke generators preserve parabolic homomorphisms on Γ_H(N)
-- statement:
--   Let $N$ be a positive integer, $H$ a subgroup of $(\mathbb Z/N)^\times$, $S$ a set of natural numbers and $\mathcal O$ a commutative ring. Write $\Gamma_H(N)$ for [`CohCarrier.GammaH N H`](def/CohCarrier_Level.html#L133), the subgroup of $\mathrm{SL}_2(\mathbb Z)$ obtained as the image under the inclusion of $\Gamma_0(N)$ of the preimage of $H$ under the character $\Gamma_0(N)\to(\mathbb Z/N)^\times$ given by the lower-right entry, and let $H^1 =$ [`CohCarrier.H1 N H 𝒪`](def/CohCarrier_Level.html#L162) be the $\mathcal O$-module of additive homomorphisms $\mathrm{Additive}\,\Gamma_H(N)\to\mathcal O$. Let $g$ be a generator in [`CohCarrier.Gen N S`](def/CohCarrier_Inst.html#L13), i.e. one of $T_\ell$ for a prime $\ell\notin S$ with $\ell\nmid N$, $U_q$ for a prime $q\mid N$, or $\langle d\rangle$ for a unit $d\in(\mathbb Z/N)^\times$, and let [`CohCarrier.opFamily N H S 𝒪 g`](def/CohCarrier_Inst.html#L91) be the associated endomorphism of $H^1$: for $T_\ell$ and $U_q$ the corestriction of $\varphi$ precomposed with the map `conjL` from the upper-triangular-type subgroup attached to $\ell$ (resp. $q$), and for $\langle d\rangle$ the operator `diamondRaw` for a chosen lift of $d$ to $\Gamma_0(N)$. The assertion is that if $\varphi\in H^1$ satisfies $\varphi(\gamma)=0$ for every $\gamma\in\Gamma_H(N)$ with $\mathrm{tr}(\gamma)^2=4$, then `opFamily N H S 𝒪 g φ` satisfies the same vanishing condition.
--
--   This is the statement that the Hecke and diamond operators act on the submodule of parabolic classes in the group cohomology of $\Gamma_H(N)$ with coefficients in $\mathcal O$, here in the concrete form that the defining vanishing on elements of trace square $4$ is preserved. It is used downstream when the Hecke module structure on parabolic cohomology of $\Gamma_H$ at auxiliary levels is needed, for instance in locating corners at non-Eisenstein maximal ideals and in the integral matrix description of the operators on a basis of parabolic homomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_opFamily_apply_mem_parabolicHoms_gammaH.lean

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.opFamily_apply_mem_parabolicHoms_gammaH (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (S : Set ℕ)
    (𝒪 : Type) [CommRing 𝒪] (g : CohCarrier.Gen N S) (φ : CohCarrier.H1 N H 𝒪)
    (hφ : φ ∈ ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N H) 𝒪) :
    CohCarrier.opFamily N H S 𝒪 g φ ∈ ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N H) 𝒪 := by sorry
