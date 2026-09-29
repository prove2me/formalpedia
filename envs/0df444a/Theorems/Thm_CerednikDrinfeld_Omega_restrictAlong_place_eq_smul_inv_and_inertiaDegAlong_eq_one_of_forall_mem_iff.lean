-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_restrictAlong_place_eq_smul_inv_and_inertiaDegAlong_eq_one_of_forall_mem_iff
-- name    : CerednikDrinfeld.Omega.restrictAlong_place_eq_smul_inv_and_inertiaDegAlong_eq_one_of_forall_mem_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/75eed5b4-545a-5a42-a3b1-075006e7c0f9
-- title:
--   Restriction of point places along a Mumford conjugation map
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra which is a field carrying a valuation with values in a linearly ordered commutative group with zero $\Gamma_0$, and let $\varpi$ be a pseudo-uniformiser for $K_0 \subseteq K$, i.e. an element $\varpi \in K_0$ whose image in $K$ has valuation $\mathfrak p$ with $0 < \mathfrak p < 1$ and such that every nonzero $a \in K_0$ satisfies $\mathfrak p^{N} \le |a| \le \mathfrak p^{-N}$ for some $N \in \mathbb N$. Let $G$ be a group, $\rho : G \to \mathrm{PGL}(2,K_0)$ a homomorphism, and assume the ring $\mathcal O =$ `Omega.HolRingOf` $\varpi\,\rho$ — the ring `Omega.holRing` $\varpi$ of functions on $\Omega =$ `Omega.upperHalfPlane` $K_0\,K$, the complement of the image of $K_0$ in $K$, that are holomorphic on each affinoid of the exhaustion attached to $\varpi$ — is a domain. Let $\Lambda_1, \Lambda_2 \le G$, and let $F_1, F_2$ be fields over $K$ together with $K$-algebra isomorphisms $e_i : F_i \cong \mathfrak M(\Lambda_i)$, where $\mathfrak M(\Lambda_i) =$ `Mumford.invariantFieldOf` $K\,G\,\mathcal O\,\Lambda_i$ is the $\Lambda_i$-invariant subfield of $\operatorname{Frac}\mathcal O$. Let $g \in G$ and let $\varphi : F_2 \to F_1$ be a $K$-algebra homomorphism which, read through $e_1$ and $e_2$ inside $\operatorname{Frac}\mathcal O$, is $f \mapsto g \cdot f$, and assume $\varphi$ is integral as a ring homomorphism. Finally let $\mathrm{pt}_i : \Omega \to$ `Place` $K\,F_i$ assign to each $z$ a place of $F_i$ over $K$ (a valuation subring of $F_i$ containing $K$, not all of $F_i$, and a principal ideal ring) subject to: $x \in \mathcal O_{\mathrm{pt}_i(z)}$ if and only if $e_i(x)$ can be written as $a/h$ with $a, h \in \mathcal O$, $h$ a non-zero-divisor and $h(z) \ne 0$; and for every such fraction lying in $\mathfrak M(\Lambda_i)$ with $h(z) \ne 0$, the residue evaluation of $\mathrm{pt}_i(z)$ at the corresponding element of $F_i$ equals $a(z)/h(z)$, this element lying in the nonunits of $\mathcal O_{\mathrm{pt}_i(z)}$ exactly when $a(z) = 0$. Then for every $z \in \Omega$: the restriction of $\mathrm{pt}_1(z)$ along $\varphi$ (the valuation subring $\varphi^{-1}\mathcal O_{\mathrm{pt}_1(z)}$ of $F_2$) equals $\mathrm{pt}_2(\rho(g)^{-1} \cdot z)$; the inertia degree along $\varphi$, namely the residue field degree of $\mathrm{pt}_1(z)$ over its restriction, equals $1$; and for every $n \in \mathbb Z$ the push-forward along $\varphi$ of the divisor $n\,[\mathrm{pt}_1(z)]$ is $n\,[\mathrm{pt}_2(\rho(g)^{-1} \cdot z)]$.
--
--   This is the equivariance of the point-to-place assignment on a Mumford quotient: conjugation by $g$ on the field of $\Lambda$-invariant meromorphic functions on the Drinfeld upper half plane translates points by $\rho(g)^{-1}$, with trivial residue extension, so that point divisors push forward to point divisors. It is used in the computation of the Cerednik–Drinfeld correspondences on divisor class groups, in particular in the statements relating $\theta$-maps on $\mathrm{Pic}^0$ to push-forward and pull-back along such maps, and in the evaluation of pull-backs of single-point divisors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_restrictAlong_place_eq_smul_inv_and_inertiaDegAlong_eq_one_of_forall_mem_iff.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

theorem CerednikDrinfeld.Omega.restrictAlong_place_eq_smul_inv_and_inertiaDegAlong_eq_one_of_forall_mem_iff
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : Omega.PseudoUniformizer K₀ K)
    (G : Type) [Group G] (ρ : G →* PGL(2, K₀)) [IsDomain (Omega.HolRingOf ϖ ρ)]
    (Λ₁ Λ₂ : Subgroup G)
    (F₁ : Type) [Field F₁] [Algebra K F₁] (e₁ : F₁ ≃ₐ[K] ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₁))
    (F₂ : Type) [Field F₂] [Algebra K F₂] (e₂ : F₂ ≃ₐ[K] ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₂))
    (g : G) (φ : F₂ →ₐ[K] F₁)
    (hφ : ∀ x : F₂, ((e₁ (φ x) : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₁)) : FractionRing (Omega.HolRingOf ϖ ρ)) =
      g • ((e₂ x : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₂)) : FractionRing (Omega.HolRingOf ϖ ρ)))
    (hφC : φ.toRingHom.IsIntegral)
    (pt₁ : ↥(Omega.upperHalfPlane K₀ K) → Place K F₁)
    (hpt₁ : ((∀ (z : ↥(Omega.upperHalfPlane K₀ K)) (x : F₁),
        x ∈ (pt₁ z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 ∧ ((e₁ x : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₁)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ K)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₁),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 →
          (pt₁ z).evalAt (e₁.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) =
            (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ∧
          (e₁.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (pt₁ z).toValuationSubring.nonunits ↔
            (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z = 0))))
    (pt₂ : ↥(Omega.upperHalfPlane K₀ K) → Place K F₂)
    (hpt₂ : ((∀ (z : ↥(Omega.upperHalfPlane K₀ K)) (x : F₂),
        x ∈ (pt₂ z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 ∧ ((e₂ x : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₂)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ K)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₂),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 →
          (pt₂ z).evalAt (e₂.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) =
            (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ∧
          (e₂.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (pt₂ z).toValuationSubring.nonunits ↔
            (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z = 0))))
    (z : ↥(Omega.upperHalfPlane K₀ K)) :
    (pt₁ z).restrictAlong φ hφC = pt₂ ((ρ g)⁻¹ • z) ∧ (pt₁ z).inertiaDegAlong φ hφC = 1 ∧
      ∀ n : ℤ, Divisor.pushforwardAlong φ hφC (Finsupp.single (pt₁ z) n) = Finsupp.single (pt₂ ((ρ g)⁻¹ • z)) n := by sorry
