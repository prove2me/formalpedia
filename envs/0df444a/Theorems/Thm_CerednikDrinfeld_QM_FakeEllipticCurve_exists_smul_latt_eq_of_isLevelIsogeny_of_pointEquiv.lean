-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_smul_latt_eq_of_isLevelIsogeny_of_pointEquiv
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_smul_latt_eq_of_isLevelIsogeny_of_pointEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/8f9196c9-b5d0-5c00-b2da-958d5fe236c5
-- title:
--   Uniformising lattice of a level-ℓ isogeny quotient
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and a $\mathbb{Q}$-algebra map $\iota$ from it to $2\times 2$ real matrices. Suppose given, for every fake elliptic curve $E$ of level $1$ over $\mathbb{C}$ (an abelian scheme over $\operatorname{Spec}\mathbb{C}$ with relative group law, commutativity, relative dimension $2$ and an action of $\Lambda$ by endomorphisms over the base), a $\mathbb{Z}$-submodule $\mathrm{latt}(E)$ of $\mathbb{C}^2$ and a bijection $e_E$ from the sections of $E.f$ over the identity of $\operatorname{Spec}\mathbb{C}$ onto $\mathbb{C}^2/\mathrm{latt}(E)$, subject to: `hL1`, that $\mathrm{latt}(E)$ is the $\mathbb{Z}$-span of the range of some $\mathbb{R}$-basis of $\mathbb{C}^2$ indexed by $\mathrm{Fin}\,4$ and is stable under $\mathrm{mulVec}$ by the complexified matrices $\iota(x)$, $x\in\Lambda$; `hE1`, that $e_E$ turns the group law on $\mathbb{C}$-points into addition; `hE2`, that $e_E$ turns the action of $x\in\Lambda$ into multiplication of representatives by the complexification of $\iota(x)$; and `hH1`, that for any $\varphi : E.A \to E'.A$ over the base which is a homomorphism for the group laws on $T$-points for all $T$ and commutes with the $\Lambda$-actions, there is $c\in\mathbb{C}$ with $c\cdot\mathrm{latt}(E)\subseteq\mathrm{latt}(E')$ inducing $\varphi$ on uniformisations, i.e. $e_{E'}(P \circ \varphi) = c\,v \bmod \mathrm{latt}(E')$ whenever $e_E(P)=v \bmod \mathrm{latt}(E)$. Let $\ell$ be a prime with $\ell\in\Lambda$, let $E,d$ be two such curves, $K$ an `ExtraLevel` $\ell$ structure on $E$ (a closed immersion $K.\mathrm{levK}$ into $E.A$ whose factoring points form a $\Lambda$-stable $\ell$-torsion subgroup of rank $\ell^2$, disjoint from $E.\mathrm{lev}$), assume `IsLevelIsogeny` $\ell$ $\langle E,K\rangle$ $d$, i.e. there are maps $\varphi : E.A\to d.A$ and $\psi : d.A\to E.A$ over the base, both homomorphisms on $T$-points and $\Lambda$-equivariant, with $\varphi\psi$ and $\psi\varphi$ the action of $\ell$, with $\varphi$ killing exactly the points factoring through $K.\mathrm{levK}$ and preserving the $\mathrm{lev}$-structures. Finally let $LK$ be a $\mathbb{Z}$-submodule of $\mathbb{C}^2$ with $v\in LK$ if and only if $e_E^{-1}(v \bmod \mathrm{latt}(E))$ factors through $K.\mathrm{levK}$. Then there exists $c'\neq 0$ in $\mathbb{C}$ with $c'\cdot\mathrm{latt}(d) = LK$.
--
--   This is the analytic dictionary step in the complex uniformisation of fake elliptic curves with auxiliary $\ell$-level structure: the lattice of the quotient curve $d$ of a level-$\ell$ isogeny is homothetic to the lattice $LK$ cut out by the kernel subgroup $K$. It is used in the construction of level-$\ell$ isogenies with prescribed sublattices, via [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_sublattice_of_pointEquiv`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_sublattice_of_pointEquiv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_smul_latt_eq_of_isLevelIsogeny_of_pointEquiv.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_smul_latt_eq_of_isLevelIsogeny_of_pointEquiv
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ)

    (latt : FakeEllipticCurve Λ 1 ℂ → Submodule ℤ (Fin 2 → ℂ))
    (e : ∀ E : FakeEllipticCurve Λ 1 ℂ,
      SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f ≃ ((Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))
    (hL1 : ∀ E : FakeEllipticCurve Λ 1 ℂ,
      (∃ b₀ : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), latt E = Submodule.span ℤ (Set.range b₀)) ∧
      (∀ x ∈ Λ, ∀ v ∈ latt E, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ latt E))
    (hE1 : ∀ (E : FakeEllipticCurve Λ 1 ℂ) (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f),
      e E (E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e E P + e E Q)
    (hE2 : ∀ (E : FakeEllipticCurve Λ 1 ℂ) (x : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
      e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
      e E (pushPt (E.act x) (E.act_over x) P) =
        ((((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))
    (hH1 : ∀ (E E' : FakeEllipticCurve Λ 1 ℂ) (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
        mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
      (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) →
      ∃ c : ℂ, (∀ v ∈ latt E, c • v ∈ latt E') ∧
        ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
          e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
          e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓΛ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (E d : FakeEllipticCurve Λ 1 ℂ) (K : E.ExtraLevel ℓ)
    (hiso : FakeEllipticCurve.IsLevelIsogeny ℓ (⟨E, K⟩ : FakeEllipticCurve.WithExtraLevel Λ 1 ℓ ℂ) d)
    (LK : Submodule ℤ (Fin 2 → ℂ))
    (hLK : ∀ v : Fin 2 → ℂ, v ∈ LK ↔ FactorsThrough K.levK ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))) :
    ∃ c' : ℂ, c' ≠ 0 ∧ c' • latt d = LK := by sorry
