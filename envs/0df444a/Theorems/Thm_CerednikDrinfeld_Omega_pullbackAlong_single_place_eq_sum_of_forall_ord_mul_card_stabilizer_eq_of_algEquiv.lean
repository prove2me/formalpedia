-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_pullbackAlong_single_place_eq_sum_of_forall_ord_mul_card_stabilizer_eq_of_algEquiv
-- name    : CerednikDrinfeld.Omega.pullbackAlong_single_place_eq_sum_of_forall_ord_mul_card_stabilizer_eq_of_algEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/c12fc6ef-22ea-5665-871f-3bd51887bc97
-- title:
--   Pull-back of a point divisor under change of level
-- statement:
--   Let $K_0$ be a field and $K$ a valued field (values in a linearly ordered commutative group with zero $\Gamma_0$) that is a $K_0$-algebra, let $\varpi$ be a pseudo-uniformiser, i.e. an element of $K_0$ whose value in $K$ lies strictly between $0$ and $1$ and such that every nonzero element of $K_0$ has value squeezed between a power of that value and the inverse power; let $G$ be a group with a homomorphism $\rho : G \to \mathrm{PGL}_2(K_0)$, and assume the ring $\mathcal O =$ `Omega.HolRingOf` $\varpi\,\rho$ — the ring of functions on the Drinfeld upper half-plane $\Omega = K \setminus \mathrm{im}(K_0 \to K)$ that are holomorphic on every affinoid of the exhaustion attached to $\varpi$ — is a domain. Let $\Lambda_1 \le \Lambda_2 \le G$. Let $F_1, F_2$ be fields over $K$ with $K$-algebra isomorphisms $e_i$ onto the invariant field $\mathfrak M(\Lambda_i) =$ `Mumford.invariantFieldOf` $K\,G\,\mathcal O\,\Lambda_i \subseteq \mathrm{Frac}(\mathcal O)$, and let $\varphi : F_2 \to F_1$ be a $K$-algebra map which, read through $e_1$ and $e_2$, is the inclusion $\mathfrak M(\Lambda_2) \subseteq \mathfrak M(\Lambda_1)$ inside $\mathrm{Frac}(\mathcal O)$, and which is integral. Let $\mathrm{pt}_i : \Omega \to$ `Place` $K\,F_i$ be maps to places (valuation subrings of $F_i$ containing $K$, proper, with principal ideals) pinned by: $x \in F_i$ lies in the valuation subring of $\mathrm{pt}_i(z)$ exactly when $e_i(x) = g/h$ for some $g \in \mathcal O$ and some non-zero-divisor $h \in \mathcal O$ with $h(z) \ne 0$; and for such a quotient lying in $\mathfrak M(\Lambda_i)$ with $h(z) \ne 0$, the residual evaluation of $\mathrm{pt}_i(z)$ at $e_i^{-1}(g/h)$ is $g(z)/h(z)$, and $e_i^{-1}(g/h)$ lies in the nonunits of that valuation subring precisely when $g(z) = 0$. Assume the fibres of $\mathrm{pt}_i$ are the orbits of $\rho(\Lambda_i)$ on $\Omega$, that $\mathrm{pt}_1$ is surjective, that $\Lambda_1$ has finite index in $\Lambda_2$ with a chosen set-theoretic section $s$ of $\Lambda_2 \to \Lambda_2/\Lambda_1$ of a finite quotient, that $F_1$ is a curve over $K$ (principal divisors, residue fields finite over $K$, and $\Omega[F_1/K]$ free of rank one), and the order law at both levels: for $z \in \Omega$, $g \ne 0$, $h$ a non-zero-divisor with $g/h \in \mathfrak M(\Lambda_i)$, the order of $e_i^{-1}(g/h)$ at $\mathrm{pt}_i(z)$ times the cardinality of the stabiliser of $z$ in $\rho(\Lambda_i)$ equals $\mathrm{ord}_{\varpi,z}(g) - \mathrm{ord}_{\varpi,z}(h)$. Assume further that every $\gamma \in \Lambda_2$ with $\rho(\gamma) = 1$ lies in $\Lambda_1$, that the fundamental identity holds for the extension of $F_2$ by $F_1$ along $\varphi$, that the degree $[F_1 : F_2]$ along $\varphi$ equals $[\Lambda_2 : \Lambda_1]$, and that the stabiliser of a given $z \in \Omega$ in $\rho(\Lambda_2)$ is finite. Then the pull-back along $\varphi$ of the divisor $1 \cdot \mathrm{pt}_2(z)$ equals $\sum_{q \in \Lambda_2/\Lambda_1} 1 \cdot \mathrm{pt}_1\bigl(\rho(s(q))^{-1} z\bigr)$, the sum of point divisors of the translates, so that multiplicities arise from coincidences among the translated points.
--
--   This is the divisor-theoretic form of the statement that the covering of Mumford quotient curves induced by a change of level $\Lambda_1 \le \Lambda_2$ has fibre over the image of $z$ the set of $\rho(\Lambda_1)$-orbits of the coset translates $\rho(s(q))^{-1}z$, with ramification recorded by repetitions in the sum; here the two curves are presented through abstract carriers $F_1, F_2$ identified with the invariant fields by $e_1, e_2$. It is used in the construction of the degree-zero divisor classes and the compatibility of push-forward with pull-back in the theta-function computations on Mumford curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_pullbackAlong_single_place_eq_sum_of_forall_ord_mul_card_stabilizer_eq_of_algEquiv.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

theorem CerednikDrinfeld.Omega.pullbackAlong_single_place_eq_sum_of_forall_ord_mul_card_stabilizer_eq_of_algEquiv
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : Omega.PseudoUniformizer K₀ K)
    (G : Type) [Group G] (ρ : G →* PGL(2, K₀)) [IsDomain (Omega.HolRingOf ϖ ρ)]

    (Λ₁ Λ₂ : Subgroup G) (hΛ : Λ₁ ≤ Λ₂)

    (F₁ : Type) [Field F₁] [Algebra K F₁] (e₁ : F₁ ≃ₐ[K] ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₁))
    (F₂ : Type) [Field F₂] [Algebra K F₂] (e₂ : F₂ ≃ₐ[K] ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₂))
    (φ : F₂ →ₐ[K] F₁)
    (hφ : ∀ x : F₂, ((e₁ (φ x) : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₁)) : FractionRing (Omega.HolRingOf ϖ ρ)) = ((e₂ x : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₂)) : FractionRing (Omega.HolRingOf ϖ ρ)))
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

    (hfib₁ : ∀ z z' : ↥(Omega.upperHalfPlane K₀ K), pt₁ z = pt₁ z' ↔ ∃ γ : ↥(Λ₁.map ρ), z' = (γ : PGL(2, K₀)) • z)
    (hfib₂ : ∀ z z' : ↥(Omega.upperHalfPlane K₀ K), pt₂ z = pt₂ z' ↔ ∃ γ : ↥(Λ₂.map ρ), z' = (γ : PGL(2, K₀)) • z)
    (hsurj₁ : Function.Surjective pt₁)

    [(Λ₁.subgroupOf Λ₂).FiniteIndex] [Fintype (↥Λ₂ ⧸ Λ₁.subgroupOf Λ₂)]
    (s : ↥Λ₂ ⧸ Λ₁.subgroupOf Λ₂ → ↥Λ₂)
    (hs : ∀ q, (QuotientGroup.mk (s q) : ↥Λ₂ ⧸ Λ₁.subgroupOf Λ₂) = q)
    [IsCurveOver K F₁]

    (hord₁ : (∀ (z : ↥(Omega.upperHalfPlane K₀ K)) (g h : Omega.HolRingOf ϖ ρ) (hg : g ≠ 0) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
      (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₁),
      (pt₁ z).ord (e₁.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) *
          (Nat.card ↥(MulAction.stabilizer ↥(Λ₁.map ρ) z) : ℤ) =
        (Omega.ordAt ϖ (show ↥(Omega.holRing ϖ) from g) z : ℤ) - (Omega.ordAt ϖ (show ↥(Omega.holRing ϖ) from h) z : ℤ)))
    (hord₂ : (∀ (z : ↥(Omega.upperHalfPlane K₀ K)) (g h : Omega.HolRingOf ϖ ρ) (hg : g ≠ 0) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
      (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Λ₂),
      (pt₂ z).ord (e₂.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) *
          (Nat.card ↥(MulAction.stabilizer ↥(Λ₂.map ρ) z) : ℤ) =
        (Omega.ordAt ϖ (show ↥(Omega.holRing ϖ) from g) z : ℤ) - (Omega.ordAt ϖ (show ↥(Omega.holRing ϖ) from h) z : ℤ)))
    (hker : ∀ γ : G, γ ∈ Λ₂ → ρ γ = 1 → γ ∈ Λ₁)

    (hFI : FundamentalIdentityAlong K φ hφC)
    (hdeg : finrankAlong K φ = Fintype.card (↥Λ₂ ⧸ Λ₁.subgroupOf Λ₂))
    (z : ↥(Omega.upperHalfPlane K₀ K)) [Finite ↥(MulAction.stabilizer ↥(Λ₂.map ρ) z)] :
    Divisor.pullbackAlong φ hφC (Finsupp.single (pt₂ z) 1) =
      ∑ q : ↥Λ₂ ⧸ Λ₁.subgroupOf Λ₂, Finsupp.single (pt₁ ((ρ ((s q : ↥Λ₂) : G))⁻¹ • z)) 1 := by sorry
