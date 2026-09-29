-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_isClosed_setOf_exists_smul_latt_eq_qmPeriodLattice_of_isProper_of_analytic
-- name    : CerednikDrinfeld.QM.IsFineModuli.isClosed_setOf_exists_smul_latt_eq_qmPeriodLattice_of_isProper_of_analytic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/5a7f6d7d-e5ed-5321-8d08-b348637e72df
-- title:
--   Properness makes the algebraic period locus closed
-- statement:
--   Fix primes $q\neq q'$ and $a,b\in\mathbb{Q}$ with `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $a>0$ or $b>0$ and, for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes\mathbb{Q}_v$ is a division algebra exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a maximal order (an order maximal among orders containing it), $\iota:\mathbb{H}[\mathbb{Q},a,b]\to M_2(\mathbb{R})$ an injective $\mathbb{Q}$-algebra map, $N\neq 0$ squarefree and prime to $q$ and $q'$, and $R\leq\Lambda$ an Eichler order of level $N$, i.e. an intersection of two maximal orders of relative index $N$. Assume the analytic dictionary for fake elliptic curves over $\mathbb{C}$ with $\Lambda$-action and level $N$: a full-rank lattice $\mathrm{latt}\,E\subset\mathbb{C}^2$ stable under $\iota(\Lambda)$, bijections $e_E$ from the $\mathbb{C}$-points of $E$ to $\mathbb{C}^2/\mathrm{latt}\,E$ that are additive for the relative group law and equivariant for the $\Lambda$-action, homomorphisms compatible with the group laws and with $\Lambda$ being exactly the homotheties $c$ with $c\cdot\mathrm{latt}\,E\subseteq\mathrm{latt}\,E'$ (in both directions) and determined by their effect on $\mathbb{C}$-points, regular functions pulling back to holomorphic functions of $v$ on the open loci where they are defined, and, near each $v_0$, a pair of regular functions giving a map $\mathbb{C}^2\to\mathbb{C}^2$ with invertible $\mathbb{C}$-linear derivative at $v_0$. Let $m\geq 3$ be coprime to $Nqq'$ and let $\pi_M:M\to\operatorname{Spec}\mathbb{C}$ with the point functor $\mathrm{ptF}$ be a fine moduli scheme for fake elliptic curves with full level $m$ (iso-invariant, compatible with base change, surjective and injective on isomorphism classes), smooth of relative dimension $1$ and proper. Then the set of $\tau$ in the upper half-plane for which there exist a fake elliptic curve $u$ over $\mathbb{C}$ with full level-$m$ structure and a scalar $c\neq 0$ with $c\cdot\mathrm{latt}\,u=\Lambda\cdot\iota(\cdot)(\tau,1)^{t}=\mathrm{qmPeriodLattice}\,\iota\,\Lambda\,\tau$, and such that for all $\lambda\in\Lambda$ and $r\in R$, whenever $N^{-1}\iota(\lambda)(\tau,1)^{t}$ is $c$ times the $e_u$-image of a $\mathbb{C}$-point factoring through the level-$N$ structure $u.\mathrm{lev}$ then so is $N^{-1}\iota(\lambda r)(\tau,1)^{t}$, is closed in the upper half-plane.
--
--   This is the closedness step in the open–closed–nonempty decomposition used to show that every point of the upper half-plane arises as the period point of an algebraic fake elliptic curve with the $R$-standard level-$N$ structure, i.e. that the complex uniformisation of the Shimura curve attached to $R$ is onto the algebraic moduli. It is cited by [`CerednikDrinfeld.QM.IsFineModuli.forall_exists_smul_latt_eq_qmPeriodLattice_of_isProper_of_analytic`](thm.html#CerednikDrinfeld.QM.IsFineModuli.forall_exists_smul_latt_eq_qmPeriodLattice_of_isProper_of_analytic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_isClosed_setOf_exists_smul_latt_eq_qmPeriodLattice_of_isProper_of_analytic.lean

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

open CategoryTheory NeronModelInfra GoodReductionJacobian IsDedekindDomain QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open AlgebraicGeometry
open AlgebraicCurve
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise

theorem CerednikDrinfeld.QM.IsFineModuli.isClosed_setOf_exists_smul_latt_eq_qmPeriodLattice_of_isProper_of_analytic
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
    (hM : IsFineModuli Λ N m M πM ptF) (hsm : SmoothOfRelativeDimension 1 πM)
    (hprop : IsProper πM) :
    IsClosed {τ : UpperHalfPlane | ∃ (u : FakeEllipticCurve.WithFullLevel Λ N m ℂ) (c : ℂ), c ≠ 0 ∧
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
