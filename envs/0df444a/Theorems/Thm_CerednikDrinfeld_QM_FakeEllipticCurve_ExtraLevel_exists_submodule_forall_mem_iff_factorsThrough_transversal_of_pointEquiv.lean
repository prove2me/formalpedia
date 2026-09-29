-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_submodule_forall_mem_iff_factorsThrough_transversal_of_pointEquiv
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_submodule_forall_mem_iff_factorsThrough_transversal_of_pointEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/3eb59eea-59c2-55fd-a329-6280569ea6b0
-- title:
--   Extra level ℓ read as a transversal sublattice of index ℓ²
-- statement:
--   Fix primes $q,q'$ and rationals $a,b$ such that $\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`: $0<a$ or $0<b$, and for each height-one prime $v$ of $\mathbb Q$ every nonzero element of $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a unit precisely when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb Z$-submodule which is an order maximal among orders, $\iota$ a $\mathbb Q$-algebra map into $M_2(\mathbb R)$, and $N$ a natural number. Assume given, for every fake elliptic curve $E$ for $(\Lambda,N)$ over $\mathbb C$, a $\mathbb Z$-submodule $\mathrm{latt}\,E\subseteq\mathbb C^2$ and a bijection $e_E$ from the $\mathbb C$-points of $E$ (sections of `E.f` over the identity of $\operatorname{Spec}\mathbb C$) onto $\mathbb C^2/\mathrm{latt}\,E$, subject to: $\mathrm{latt}\,E$ is the $\mathbb Z$-span of an $\mathbb R$-basis of $\mathbb C^2$ and is stable under $\iota(x)$, $x\in\Lambda$, acting by `mulVec` after complexification; $e_E$ carries the group law `E.L` to addition; and $e_E$ intertwines the action of $x\in\Lambda$ on points with $\iota(x)$. Assume also a second assignment $\mathrm{lattLev}$ such that $v\in\mathrm{lattLev}\,E$ iff $v \bmod \mathrm{latt}\,E$ is $e_E(P)$ for some point $P$ factoring through `E.lev`, with $\mathrm{latt}\,E\le\mathrm{lattLev}\,E$, $\Lambda$-stability, $N\cdot\mathrm{lattLev}\,E\subseteq\mathrm{latt}\,E$, and $\mathrm{latt}\,E$ of index $N^2$ in $\mathrm{lattLev}\,E$. Let $\ell$ be prime, $E$ such a curve, $K$ an `ExtraLevel` of $E$ of level $\ell$ (a closed immersion $\mathrm{lev}_K$ whose points form a $\Lambda$-stable subgroup of $\ell$-torsion points meeting `E.lev` trivially, finite flat of rank $\ell^2$ with geometric fibres $(\mathbb Z/\ell)^2$), $\tau$ in the upper half-plane and $c\ne 0$ with $c\cdot\mathrm{latt}\,E=L_\tau:=\iota$-period lattice `qmPeriodLattice ι Λ τ`, the image of $\Lambda$ under `qmPeriodMap ι τ`. The conclusion is the existence of a $\mathbb Z$-submodule $L_K\subseteq\mathbb C^2$ with: $v\in L_K$ iff $e_E^{-1}(v\bmod \mathrm{latt}\,E)$ factors through $\mathrm{lev}_K$; $\mathrm{latt}\,E\le L_K$; $(c\ell)\cdot L_K\le L_\tau$; $\ell\, L_\tau\subseteq (c\ell)\cdot L_K$; $(c\ell)\cdot L_K$ is stable under $\iota(y)$ for $y\in\Lambda$; $(c\ell)\cdot L_K$ has index $\ell^2$ in $L_\tau$; and transversality to the level: if $v\in\mathrm{lattLev}\,E$ and $(\ell c)\cdot v\in (c\ell)\cdot L_K$ then $v\in\mathrm{latt}\,E$.
--
--   This is the lattice translation, via the complex uniformisation dictionary for fake elliptic curves with level-$N$ structure, of an extra level-$\ell$ subgroup scheme: it produces the corresponding $\iota(\Lambda)$-stable sublattice of index $\ell^2$ in the quaternionic period lattice at $\tau$, together with the disjointness of $K$ from the level structure expressed as a transversality condition between lattices. It is used to build the level-$\ell$ isogeny of the Hecke correspondence at $\ell$ and, through that, in the integrality statement for the coarse moduli description over $\mathbb C$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_submodule_forall_mem_iff_factorsThrough_transversal_of_pointEquiv.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_submodule_forall_mem_iff_factorsThrough_transversal_of_pointEquiv
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) {N : ℕ}

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

    (lattLev : FakeEllipticCurve Λ N ℂ → Submodule ℤ (Fin 2 → ℂ))
    (hLev : ∀ E : FakeEllipticCurve Λ N ℂ,
      (∀ v : Fin 2 → ℂ, v ∈ lattLev E ↔
        ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f,
          FactorsThrough E.lev P ∧ e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)) ∧
      latt E ≤ lattLev E ∧
      (∀ x ∈ Λ, ∀ v ∈ lattLev E, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ lattLev E) ∧
      (∀ v ∈ lattLev E, (N : ℤ) • v ∈ latt E) ∧
      (latt E).toAddSubgroup.relIndex (lattLev E).toAddSubgroup = N ^ 2)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (E : FakeEllipticCurve Λ N ℂ) (K : E.ExtraLevel ℓ)
    (τ : UpperHalfPlane) (c : ℂ) (hc : c ≠ 0) (hcL : c • latt E = qmPeriodLattice ι Λ τ) :
    ∃ LK : Submodule ℤ (Fin 2 → ℂ),
      (∀ v : Fin 2 → ℂ, v ∈ LK ↔ FactorsThrough K.levK ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))) ∧
      latt E ≤ LK ∧
      (c * ℓ) • LK ≤ qmPeriodLattice ι Λ τ ∧
      (∀ v ∈ qmPeriodLattice ι Λ τ, (ℓ : ℤ) • v ∈ (c * ℓ) • LK) ∧
      (∀ y ∈ Λ, ∀ v ∈ (c * ℓ) • LK, ((ι y).map (algebraMap ℝ ℂ)).mulVec v ∈ (c * ℓ) • LK) ∧
      ((c * ℓ) • LK).toAddSubgroup.relIndex (qmPeriodLattice ι Λ τ).toAddSubgroup = ℓ ^ 2 ∧

      (∀ v ∈ lattLev E, ((ℓ : ℂ) * c) • v ∈ (c * ℓ) • LK → v ∈ latt E) := by sorry
