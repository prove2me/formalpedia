-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_forall_exists_algebraicFamily_withExtraLevel_isPullback_smul_latt_eq_of_analytic
-- name    : CerednikDrinfeld.QM.IsFineModuli.forall_exists_algebraicFamily_withExtraLevel_isPullback_smul_latt_eq_of_analytic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/5e92f976-07ff-5a69-b2bb-9a71b07ea7d5
-- title:
--   Local algebraic families of fake elliptic curves with extra level ℓ
-- statement:
--   Fix primes $q\neq q'$ and rationals $a,b$ with $\mathbb{H}[\mathbb{Q},a,b]$ indefinite ($0<a$ or $0<b$) and ramified exactly at $q,q'$ (its completion at a finite place $v$ is a division algebra iff $q\in v$ or $q'\in v$), a maximal order $\Lambda$, an injective $\mathbb{Q}$-algebra map $\iota$ into $M_2(\mathbb{R})$, a squarefree $N\neq 0$ prime to $q,q'$, an Eichler order $R\le\Lambda$ of level $N$ (an intersection of two maximal orders of relative index $N$), and a module $J'\supseteq\Lambda$ with $\Lambda J'\subseteq J'$, $NJ'\subseteq\Lambda$, $[J':\Lambda]=N^2$ and $\{x\in\Lambda: J'x\subseteq J'\}=R$. Fix a prime $\ell\notin\{q,q'\}$ and $t\in R$ with $\mathrm{nrd}\,t=\ell$ satisfying $\ell J'+\Lambda t=J't$ elementwise. Assume the analytic dictionary over $\mathbb{C}$, given as hypotheses: a lattice $\mathrm{latt}(E)$ and a bijection $e_E$ from the $\mathbb{C}$-points of each fake elliptic curve $E$ of level $N$ onto $\mathbb{C}^2/\mathrm{latt}(E)$, with $\mathrm{latt}(E)$ spanned by an $\mathbb{R}$-basis and $\iota(\Lambda)$-stable, $e_E$ additive and $\Lambda$-equivariant via $\iota$; homomorphisms $E\to E'$ corresponding exactly to scalars $c$ with $c\,\mathrm{latt}(E)\subseteq\mathrm{latt}(E')$ and determined by their effect on points; regular functions pulling back to holomorphic functions of $v$; and local charts with invertible derivative. Fix $m\ge 3$ with $\ell\mid m$ and a fine moduli scheme $(M,\pi_M,\mathrm{ptF})$ for level-$N$ fake elliptic curves with full level $m$ (the point map is isomorphism-invariant, pullback-compatible, surjective and injective), with $\pi_M$ proper and smooth of relative dimension $1$. Then for every $\tau_0$ in the upper half plane there are a finite-type $\mathbb{C}$-algebra $S$ which is a domain, a fake elliptic curve $\mathcal{A}$ over $S$ of level $N$ with extra level $\ell$, and an open $W\ni\tau_0$ such that for each $\tau\in W$ there are $E'$ over $\mathbb{C}$ of the same type and a $\mathbb{C}$-algebra map $\sigma:S\to\mathbb{C}$ with $E'$ the pullback of $\mathcal{A}$ along $\sigma$ (a pullback square compatible with the group law, $\Lambda$-equivariant, and carrying points factoring through the level-$N$ and extra-level subschemes to such points), together with $c\neq 0$ with $c\cdot\mathrm{latt}(E'_1)=\iota(\Lambda)\binom{\tau}{1}$, such that: the set of $\lambda\in\Lambda$ for which $N^{-1}\iota(\lambda)\binom{\tau}{1}=c\,v$ for some $v$ representing a point factoring through the level-$N$ structure of $E'_1$ is stable under right multiplication by $R$; and a vector $v$ represents a point factoring through the extra level of $E'$ iff $\iota(yt)\binom{\tau}{1}=(c\ell)\,v$ for some $y\in\Lambda$.
--
--   This is the local uniformisation chart for the moduli problem of pairs (fake elliptic curve with level-$N$ structure, extra level structure at $\ell$): every period lattice near a given $\tau_0$ in the upper half plane is realised by a member of a single algebraic family over an integral base. It is used to prove that the coarse moduli scheme of such pairs over $\mathbb{C}$ is integral, in [`CerednikDrinfeld.QM.IsCoarseModuliT.isIntegral_of_complex_of_squarefree_of_dvd`](thm.html#CerednikDrinfeld.QM.IsCoarseModuliT.isIntegral_of_complex_of_squarefree_of_dvd); no relation between $\ell$ and $N$ is assumed, so the statement covers the case $\ell\mid N$ in which a pair is not the same as a level-$N\ell$ structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_forall_exists_algebraicFamily_withExtraLevel_isPullback_smul_latt_eq_of_analytic.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open AlgebraicCurve
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise

theorem CerednikDrinfeld.QM.IsFineModuli.forall_exists_algebraicFamily_withExtraLevel_isPullback_smul_latt_eq_of_analytic
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) (hqq' : q' ≠ q)
    {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)

    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J'))

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') (t : ℍ[ℚ, a, b]) (ht : t ∈ R) (hnrd : nrd t = (ℓ : ℚ))
    (hlev : ∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t = x) ↔ ∃ j ∈ J', j * t = x)

    (latt : FakeEllipticCurve Λ N ℂ → Submodule ℤ (Fin 2 → ℂ))
    (e : ∀ E : FakeEllipticCurve Λ N ℂ,
      SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f ≃ ((Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))

    (hL1 : ∀ E : FakeEllipticCurve Λ N ℂ,
        (∃ b₀ : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), latt E = Submodule.span ℤ (Set.range b₀)) ∧
        (∀ x ∈ Λ, ∀ v ∈ latt E, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ latt E))

    (hE1 : ∀ (E : FakeEllipticCurve Λ N ℂ) (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f),
        e E (E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e E P + e E Q)

    (hE2 : ∀ (E : FakeEllipticCurve Λ N ℂ) (x : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
        e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
        e E (pushPt (E.act x) (E.act_over x) P) =
          ((((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))

    (hH1 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
          mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
        (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) →
        ∃ c : ℂ, (∀ v ∈ latt E, c • v ∈ latt E') ∧
          ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
            e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
            e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup))

    (hH2 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (c : ℂ), (∀ v ∈ latt E, c • v ∈ latt E') →
        ∃ (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
            mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
          (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧
          ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
            e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
            e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup))

    (hH3 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (φ ψ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (hψ : ψ ≫ E'.f = E.f),
        (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f, mapPt φ hφ P = mapPt ψ hψ P) → φ = ψ)

    (hAN : ∀ (E : FakeEllipticCurve Λ N ℂ) (U : E.A.Opens) (f : Γ(E.A, U)),
        IsOpen {v : Fin 2 → ℂ | ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U} ∧
        ∃ F : (Fin 2 → ℂ) → ℂ,
          DifferentiableOn ℂ F {v : Fin 2 → ℂ | ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U} ∧
          ∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U),
            F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
              ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f))

    (hCOV : ∀ (E : FakeEllipticCurve Λ N ℂ) (v₀ : Fin 2 → ℂ),
        ∃ (U : E.A.Opens) (f₁ f₂ : Γ(E.A, U)) (ε : ℝ) (D : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ))
          (F : (Fin 2 → ℂ) → (Fin 2 → ℂ)),
          0 < ε ∧
          (∀ v ∈ Metric.ball v₀ ε, ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U) ∧
          (∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U),
            v ∈ Metric.ball v₀ ε →
            F v = ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
                      ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f₁),
                    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
                      ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f₂)]) ∧
          HasFDerivAt F (D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) v₀)

    (m : ℕ) (hm : 3 ≤ m)
    (hℓm : ℓ ∣ m)
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of ℂ))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of ℂ)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM)
    (hM : IsFineModuli Λ N m M πM ptF) (hsm : SmoothOfRelativeDimension 1 πM)
    (hprop : IsProper πM) :
    ∀ τ₀ : UpperHalfPlane,
      ∃ (S : Type) (_ : CommRing S) (_ : IsDomain S) (_ : Algebra ℂ S) (_ : Algebra.FiniteType ℂ S)
        (𝒜 : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (W : Set UpperHalfPlane),
        IsOpen W ∧ τ₀ ∈ W ∧
        ∀ τ ∈ W, ∃ (E' : FakeEllipticCurve.WithExtraLevel Λ N ℓ ℂ) (σ : S →ₐ[ℂ] ℂ),
          FakeEllipticCurve.WithExtraLevel.IsPullback σ.toRingHom 𝒜 E' ∧
          ∃ c : ℂ, c ≠ 0 ∧ c • latt E'.1 = qmPeriodLattice ι Λ τ ∧
            (∀ (lam : ℍ[ℚ, a, b]), lam ∈ Λ → ∀ r ∈ R,
              (∃ v : Fin 2 → ℂ,
                (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E'.1.f,
                  FactorsThrough E'.1.lev P ∧ e E'.1 P = (v : (Fin 2 → ℂ) ⧸ (latt E'.1).toAddSubgroup)) ∧
                c • v = ((N : ℂ)⁻¹) • qmPeriodMap ι τ lam) →
              (∃ v : Fin 2 → ℂ,
                (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E'.1.f,
                  FactorsThrough E'.1.lev P ∧ e E'.1 P = (v : (Fin 2 → ℂ) ⧸ (latt E'.1).toAddSubgroup)) ∧
                c • v = ((N : ℂ)⁻¹) • qmPeriodMap ι τ (lam * r))) ∧

            (∀ v : Fin 2 → ℂ,
              FactorsThrough E'.2.levK ((e E'.1).symm (v : (Fin 2 → ℂ) ⧸ (latt E'.1).toAddSubgroup)) ↔
                ∃ y ∈ Λ, qmPeriodMap ι τ (y * t) = (c * (ℓ : ℂ)) • v) := by sorry
