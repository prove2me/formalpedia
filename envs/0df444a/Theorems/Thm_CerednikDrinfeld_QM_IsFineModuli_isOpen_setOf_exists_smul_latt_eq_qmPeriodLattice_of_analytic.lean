-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_isOpen_setOf_exists_smul_latt_eq_qmPeriodLattice_of_analytic
-- name    : CerednikDrinfeld.QM.IsFineModuli.isOpen_setOf_exists_smul_latt_eq_qmPeriodLattice_of_analytic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/8a1b73ea-b8f3-5612-97f5-768abde587f1
-- title:
--   Openness of the uniformised locus in H
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$, let $a,b\in\mathbb Q$ and suppose `hB`: $\mathbb H[\mathbb Q,a,b]$ satisfies $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the completed algebra $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ has all nonzero elements invertible exactly when $q\in v$ or $q'\in v$. Let $\Lambda$ be a $\mathbb Z$-submodule that is an order maximal among the orders containing it, $\iota:\mathbb H[\mathbb Q,a,b]\to M_2(\mathbb R)$ an injective $\mathbb Q$-algebra map, $N\neq 0$ squarefree with $q\nmid N$, $q'\nmid N$, and $R\le\Lambda$ an Eichler order of level $N$, i.e. $R=\Lambda_1\cap\Lambda_2$ for maximal orders $\Lambda_i$ with $[\Lambda_1:R]=N$. Assume the analytic dictionary for fake elliptic curves over $\mathbb C$ with $\Lambda$-action and level $N$: a lattice $\mathrm{latt}\,E\subset\mathbb C^2$ (spanned over $\mathbb Z$ by an $\mathbb R$-basis of $\mathbb C^2$ and stable under $\iota(\Lambda)$) together with a bijection $e_E$ from the sections of $E.f$ over $\mathrm{id}_{\operatorname{Spec}\mathbb C}$ to $\mathbb C^2/\mathrm{latt}\,E$ which is additive for the relative group law (`hE1`) and $\Lambda$-equivariant through $\iota$ (`hE2`); morphisms over $\operatorname{Spec}\mathbb C$ respecting the group law and commuting with the $\Lambda$-action are exactly the homotheties $c$ with $c\cdot\mathrm{latt}\,E\subseteq\mathrm{latt}\,E'$ (`hH1`, `hH2`), morphisms are determined by their effect on $\mathbb C$-points (`hH3`), sections of $\mathcal O_{E.A}$ pull back to functions holomorphic on the open locus of $v\in\mathbb C^2$ lying over the given open set (`hAN`), and pairs of sections give local charts with invertible derivative at any prescribed $v_0$ (`hCOV`). Let $m\geq 3$ be coprime to $Nqq'$, and let $\pi_M:M\to\operatorname{Spec}\mathbb C$ with a point assignment $\mathrm{ptF}$ be a fine moduli scheme for fake elliptic curves with full level $m$ (isomorphism-invariant, compatible with base change, surjective, and injective up to isomorphism), with $\pi_M$ smooth of relative dimension $1$. Then the set of $\tau$ in the upper half-plane for which there are $u$, a fake elliptic curve over $\mathbb C$ with full level-$m$ structure, and $c\neq 0$ with $c\cdot\mathrm{latt}\,u_1=\iota$-period lattice $\Lambda\cdot\binom{\tau}{1}$, such that for all $\lambda\in\Lambda$ and $r\in R$, whenever $N^{-1}\iota(\lambda)\binom{\tau}{1}=c\,v$ for some $v$ representing a $\mathbb C$-point of $u_1$ factoring through the level morphism $u_1.\mathrm{lev}$, the same holds for $\lambda r$, is open in the upper half-plane.
--
--   This is the openness assertion in the complex uniformisation of Shimura curves: the locus of $\tau$ whose quaternionic period lattice is realised, up to homothety, by an algebraic fake elliptic curve carrying the $R$-standard level-$N$ structure is open. It is one of the three legs (open, closed, non-empty) combined by connectedness of the upper half-plane in [`CerednikDrinfeld.QM.IsFineModuli.forall_exists_smul_latt_eq_qmPeriodLattice_of_isProper_of_analytic`](thm.html#CerednikDrinfeld.QM.IsFineModuli.forall_exists_smul_latt_eq_qmPeriodLattice_of_isProper_of_analytic), and it uses the local period chart at the moduli point together with the Fuchsian-group invariance of the condition on the level structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_isOpen_setOf_exists_smul_latt_eq_qmPeriodLattice_of_analytic.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise

theorem CerednikDrinfeld.QM.IsFineModuli.isOpen_setOf_exists_smul_latt_eq_qmPeriodLattice_of_analytic
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) (hqq' : q' ≠ q)
    {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)

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

    (m : ℕ) (hm : 3 ≤ m) (hmc : m.Coprime (N * q * q'))
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of ℂ))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of ℂ)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM)
    (hM : IsFineModuli Λ N m M πM ptF) (hsm : SmoothOfRelativeDimension 1 πM) :
    IsOpen {τ : UpperHalfPlane | ∃ (u : FakeEllipticCurve.WithFullLevel Λ N m ℂ) (c : ℂ), c ≠ 0 ∧
        c • latt u.1 = qmPeriodLattice ι Λ τ ∧

          ∀ (lam : ℍ[ℚ, a, b]), lam ∈ Λ → ∀ r ∈ R,
            (∃ v : Fin 2 → ℂ,
              (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) u.1.f,
                FactorsThrough u.1.lev P ∧ e u.1 P = (v : (Fin 2 → ℂ) ⧸ (latt u.1).toAddSubgroup)) ∧
              c • v = ((N : ℂ)⁻¹) • qmPeriodMap ι τ lam) →
            (∃ v : Fin 2 → ℂ,
              (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) u.1.f,
                FactorsThrough u.1.lev P ∧ e u.1 P = (v : (Fin 2 → ℂ) ⧸ (latt u.1).toAddSubgroup)) ∧
              c • v = ((N : ℂ)⁻¹) • qmPeriodMap ι τ (lam * r))} := by sorry
