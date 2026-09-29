-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_factor_comp_iota_eq_iota_comp_factor
-- name    : CerednikDrinfeld.FormalOmega.MumfordGlueLevel.factor_comp_iota_eq_iota_comp_factor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/0521f66f-1a30-5829-b300-56b2bed05b5d
-- title:
--   Level compatibility of the vertex inclusion in Mumford gluing data
-- statement:
--   Fix a prime $r$ and a commutative domain $\mathcal{O}$ that is a discrete valuation ring, an irreducible element $\pi \in \mathcal{O}$ whose residue ring $\mathcal{O}/(\pi)$ has exactly $r$ elements, and a field $K_0$ that is an $\mathcal{O}$-algebra and a fraction field of $\mathcal{O}$; let $g_1 \in \mathrm{GL}_2(K_0)$ be the matrix $\mathrm{diag}(\pi,1)$, let $N$ be a subgroup of $\mathrm{PGL}_2(K_0)$, let $n$ be a natural number, and let $L$, $L'$ be Mumford gluing data (in the sense of `MumfordGlueLevel`) for these data at levels $n$ and $n+1$. Write $V =$ `chartVRing` $\mathcal{O}\,r$, the localisation of $\mathcal{O}[X]$ away from $X^r - X$, and $A =$ `chartERing` $\mathcal{O}\,\pi\,r$, the localisation of $\mathcal{O}[\xi,\eta]/(\xi\eta - \pi)$ away from the edge discriminant. Each datum carries an $\mathcal{O}$-algebra map $\iota$ from $A/(\pi^{m+1})$ to $V/(\pi^{m+1})$ ($m$ its level) sending the class of $\xi$ to that of $\zeta$, with $\iota(\bar\eta)\cdot\bar\zeta = \pi$, and exhibiting the target as the localisation of the source away from $\bar\xi$. The assertion is that the square of reduction maps commutes: the canonical quotient map $V/(\pi^{n+2}) \to V/(\pi^{n+1})$ precomposed with $L'.\iota$ equals $L.\iota$ precomposed with the canonical quotient map $A/(\pi^{n+2}) \to A/(\pi^{n+1})$, as ring homomorphisms.
--
--   This is the compatibility, with respect to reduction modulo successive powers of $\pi$, of the vertex-chart inclusion carried by Mumford gluing data for the $\pi$-adic formal upper half plane. It is used in the transition step [`CerednikDrinfeld.FormalOmega.MumfordGlueLevel.exists_transition`](thm.html#CerednikDrinfeld.FormalOmega.MumfordGlueLevel.exists_transition), where level-$(n+1)$ data must be compared with its reduction to level $n$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_factor_comp_iota_eq_iota_comp_factor.lean

import Definitions.Def_CerednikDrinfeld_MumfordGlueLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.MumfordGlueLevel.factor_comp_iota_eq_iota_comp_factor
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀))) (n : ℕ)
    (L : MumfordGlueLevel 𝒪 π K₀ r g₁ N n) (L' : MumfordGlueLevel 𝒪 π K₀ r g₁ N (n + 1)) :
    (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
        (pow_dvd_pow (algebraMap 𝒪 (chartVRing 𝒪 r) π) (Nat.le_succ (n + 1))))).comp L'.ι.toRingHom =
      L.ι.toRingHom.comp (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
        (pow_dvd_pow (algebraMap 𝒪 (chartERing 𝒪 π r) π) (Nat.le_succ (n + 1))))) := by sorry
