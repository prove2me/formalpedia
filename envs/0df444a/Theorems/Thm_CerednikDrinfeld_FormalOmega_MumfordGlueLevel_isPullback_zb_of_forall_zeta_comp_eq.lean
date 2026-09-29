-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_isPullback_zb_of_forall_zeta_comp_eq
-- name    : CerednikDrinfeld.FormalOmega.MumfordGlueLevel.isPullback_zb_of_forall_zeta_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/75c1f084-1ff4-5d71-8d28-a02d5a83c1df
-- title:
--   Consecutive Mumford gluing levels form a cartesian square
-- statement:
--   Let $r$ be a prime, let $\mathcal O$ be a domain that is a discrete valuation ring, let $\pi \in \mathcal O$ be irreducible with $\#(\mathcal O/(\pi)) = r$, let $K_0$ be a fraction field of $\mathcal O$, and let $g_1 \in GL_2(K_0)$ be the diagonal matrix $\mathrm{diag}(\pi, 1)$. Fix a subgroup $N \le PGL_2(K_0)$ and $n \in \mathbb N$, and let $L$, $L'$ be Mumford gluing data of levels $n$ and $n+1$ for these parameters: each consists of a scheme $Z$ with a flat separated morphism $zb$ to $\operatorname{Spec}(\mathcal O/(\pi^{m+1}))$ ($m = n$, resp. $n+1$), a family of open immersions $\zeta_h$ from $\operatorname{Spec}$ of the edge chart ring `chartERing 𝒪 π r` modulo $\pi^{m+1}$ into $Z$ indexed by $h \in GL_2(K_0)$, lying over the base, finitely many of which cover $Z$, invariant under left translation by elements of $GL_2(K_0)$ whose class lies in $N$, together with the localisation comparison $\iota$ with the vertex chart ring and the data $\tau$ describing the associated Deligne data. Let $zt : L.Z \to L'.Z$ be a morphism which on every chart is the reduction map, i.e. $\zeta_h$ followed by $zt$ equals the map induced by the quotient $\mathcal O$-algebra surjection of edge chart rings modulo $\pi^{n+2}$ onto modulo $\pi^{n+1}$, followed by $L'.\zeta_h$, for every $h \in GL_2(K_0)$. Then the square formed by $zt$, $L.zb$, $L'.zb$ and $\operatorname{Spec}$ of the reduction $\mathcal O/(\pi^{n+2}) \to \mathcal O/(\pi^{n+1})$ is cartesian; that is, $L.Z$ is the fibre product of $L'.Z$ and $\operatorname{Spec}(\mathcal O/(\pi^{n+1}))$ over $\operatorname{Spec}(\mathcal O/(\pi^{n+2}))$.
--
--   This is the compatibility step in the Mumford-style construction of the formal model of the $p$-adic upper half plane by gluing levels: it says that a level-$n$ gluing datum mapping chartwise to a level-$(n+1)$ datum realises the level-$n$ scheme as the truncation of the level-$(n+1)$ scheme over the truncated base. It is used in the construction of transition morphisms between consecutive levels ([`CerednikDrinfeld.FormalOmega.MumfordGlueLevel.exists_transition`](thm.html#CerednikDrinfeld.FormalOmega.MumfordGlueLevel.exists_transition)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_isPullback_zb_of_forall_zeta_comp_eq.lean

import Definitions.Def_CerednikDrinfeld_MumfordGlueLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.MumfordGlueLevel.isPullback_zb_of_forall_zeta_comp_eq
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀))) (n : ℕ)
    (L : MumfordGlueLevel 𝒪 π K₀ r g₁ N n) (L' : MumfordGlueLevel 𝒪 π K₀ r g₁ N (n + 1))
    (zt : L.Z ⟶ L'.Z)
    (hzt : ∀ h : Matrix.GeneralLinearGroup (Fin 2) K₀,
      L.ζ h ≫ zt = Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 (chartERing 𝒪 π r) π) (Nat.le_succ (n + 1)))))) ≫ L'.ζ h) :
    IsPullback zt L.zb L'.zb
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))) := by sorry
