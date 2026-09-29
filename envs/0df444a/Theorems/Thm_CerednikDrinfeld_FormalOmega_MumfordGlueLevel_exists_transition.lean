-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_exists_transition
-- name    : CerednikDrinfeld.FormalOmega.MumfordGlueLevel.exists_transition
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/fb005339-242d-5a12-86b9-9748b284068c
-- title:
--   Cartesian transition between consecutive Mumford gluing levels
-- statement:
--   Fix a prime $r$, a domain $\mathcal{O}$ which is a discrete valuation ring, an irreducible element $\pi \in \mathcal{O}$ whose residue ring $\mathcal{O}/(\pi)$ has exactly $r$ elements, and a field $K_0$ that is an $\mathcal{O}$-algebra and a fraction field of $\mathcal{O}$; let $g_1 \in \mathrm{GL}_2(K_0)$ be the element whose matrix is $\mathrm{diag}(\pi,1)$, let $N$ be any subgroup of $\mathrm{PGL}_2(K_0)$, and let $n$ be a natural number. Given gluing data $L$ of level $n$ and $L'$ of level $n+1$ in the sense of `MumfordGlueLevel` — each consisting of a flat separated scheme $Z$ over $\mathrm{Spec}(\mathcal{O}/\pi^{n+1})$, respectively $\mathrm{Spec}(\mathcal{O}/\pi^{n+2})$, together with charts $\zeta_h$ from the spectrum of the edge chart ring `chartERing 𝒪 π r` modulo $\pi^{n+1}$ (resp. $\pi^{n+2}$) indexed by $h \in \mathrm{GL}_2(K_0)$, open immersions over the base, a finite subcover, invariance under left multiplication by elements of $N$, a localisation $\iota$ into the vertex chart ring quotient, and transport isomorphisms — the assertion is that there is a morphism $z_t : L.Z \to L'.Z$ such that the square formed by $z_t$, the structure morphisms $L.zb$ and $L'.zb$, and the closed immersion $\mathrm{Spec}(\mathcal{O}/\pi^{n+1}) \to \mathrm{Spec}(\mathcal{O}/\pi^{n+2})$ induced by the reduction map $\mathcal{O}/\pi^{n+2} \to \mathcal{O}/\pi^{n+1}$ is cartesian, and such that for every $h \in \mathrm{GL}_2(K_0)$ the chart $L.\zeta_h$ followed by $z_t$ equals the spectrum of the corresponding reduction map on the edge chart ring quotients followed by $L'.\zeta_h$.
--
--   This is the transition step of Mumford's gluing construction over $\mathcal{O}$: the level-$n$ scheme is recovered as the reduction modulo $\pi^{n+1}$ of the level-$(n+1)$ scheme, compatibly with all edge charts. It is used in assembling a compatible system of levels into the formal Čerednik–Drinfeld model, in `nonempty_mumfordGlueCore_of_isSchottky`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_exists_transition.lean

import Definitions.Def_CerednikDrinfeld_MumfordGlueLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.MumfordGlueLevel.exists_transition
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀))) (n : ℕ)
    (L : MumfordGlueLevel 𝒪 π K₀ r g₁ N n) (L' : MumfordGlueLevel 𝒪 π K₀ r g₁ N (n + 1)) :
    ∃ zt : L.Z ⟶ L'.Z,
      IsPullback zt L.zb L'.zb
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))) ∧
      ∀ h : Matrix.GeneralLinearGroup (Fin 2) K₀,
        L.ζ h ≫ zt = Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
          (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 (chartERing 𝒪 π r) π) (Nat.le_succ (n + 1)))))) ≫ L'.ζ h := by sorry
