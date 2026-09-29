-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_isPullback_Spec_map_factor_chartERing
-- name    : CerednikDrinfeld.FormalOmega.isPullback_Spec_map_factor_chartERing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/5ffa5a0f-0fb0-5b3b-b80b-a586f96f138c
-- title:
--   Cartesian reduction square for truncated edge-chart rings
-- statement:
--   Let $\mathcal O$ be a commutative ring, $\pi\in\mathcal O$ and $r,n$ natural numbers (no primality of $r$ is assumed), and write $A:=$ `chartERing 𝒪 π r`, the localisation of $\mathrm{MvPolynomial}(\mathrm{Fin}\,2,\mathcal O)/(\mathrm{edgeRel})$ away from the element `edgeQuot.discr 𝒪 π r`, regarded as an $\mathcal O$-algebra via its structure map $\varphi=$ `algebraMap 𝒪 A`. Suppose given ring homomorphisms $q:\mathcal O/(\pi^{n+1})\to A/(\varphi(\pi)^{n+1})$ and $q':\mathcal O/(\pi^{n+2})\to A/(\varphi(\pi)^{n+2})$ which are compatible with the structure map, in the sense that $q$ precomposed with the quotient map $\mathcal O\to\mathcal O/(\pi^{n+1})$ equals $\varphi$ followed by the quotient map $A\to A/(\varphi(\pi)^{n+1})$, and likewise for $q'$ in degree $n+2$. Then the square of affine schemes whose two maps out of $\operatorname{Spec}\big(A/(\varphi(\pi)^{n+1})\big)$ are $\operatorname{Spec}$ of the canonical surjection $A/(\varphi(\pi)^{n+2})\to A/(\varphi(\pi)^{n+1})$ and $\operatorname{Spec} q$, and whose two maps into $\operatorname{Spec}\big(\mathcal O/(\pi^{n+2})\big)$ are $\operatorname{Spec} q'$ and $\operatorname{Spec}$ of the surjection $\mathcal O/(\pi^{n+2})\to\mathcal O/(\pi^{n+1})$, is a pullback square in the category of schemes.
--
--   This is the chart-level statement that reduction modulo $\pi^{n+1}$ of an edge chart of Drinfeld's formal upper half plane is obtained from its reduction modulo $\pi^{n+2}$ by base change along $\mathcal O/(\pi^{n+2})\to\mathcal O/(\pi^{n+1})$, i.e. that $A/\pi^{n+1}=\big(A/\pi^{n+2}\big)\otimes_{\mathcal O/\pi^{n+2}}\mathcal O/\pi^{n+1}$. It feeds the compatibility of successive truncation levels in the Mumford gluing construction, where it is used by [`CerednikDrinfeld.FormalOmega.MumfordGlueLevel.isPullback_zb_of_forall_zeta_comp_eq`](thm.html#CerednikDrinfeld.FormalOmega.MumfordGlueLevel.isPullback_zb_of_forall_zeta_comp_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_isPullback_Spec_map_factor_chartERing.lean

import Definitions.Def_CerednikDrinfeld_MumfordGlueLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.isPullback_Spec_map_factor_chartERing
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r n : ℕ)
    (q : (𝒪 ⧸ Ideal.span {π ^ (n + 1)}) →+* ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})))
    (hq : q.comp (Ideal.Quotient.mk (Ideal.span {π ^ (n + 1)})) =
      (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})).comp (algebraMap 𝒪 (chartERing 𝒪 π r)))
    (q' : (𝒪 ⧸ Ideal.span {π ^ (n + 1 + 1)}) →+* ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1 + 1)})))
    (hq' : q'.comp (Ideal.Quotient.mk (Ideal.span {π ^ (n + 1 + 1)})) =
      (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1 + 1)})).comp (algebraMap 𝒪 (chartERing 𝒪 π r))) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 (chartERing 𝒪 π r) π) (Nat.le_succ (n + 1)))))))
      (Spec.map (CommRingCat.ofHom q))
      (Spec.map (CommRingCat.ofHom q'))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))) := by sorry
