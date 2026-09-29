-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_factorsThrough_levK_symm_iff_exists_qmPeriodMap_mul_eq_of_forall_geomPoint
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.factorsThrough_levK_symm_iff_exists_qmPeriodMap_mul_eq_of_forall_geomPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/25adc0a7-ab2e-5d44-bf50-ceebe30fd894
-- title:
--   Extra level at ℓ as the period lattice of Λ t
-- statement:
--   Fix $a,b\in\mathbb{Q}$, a $\mathbb{Z}$-submodule $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$, $N\in\mathbb{N}$, a $\mathbb{Q}$-algebra map $\iota\colon\mathbb{H}[\mathbb{Q},a,b]\to M_2(\mathbb{R})$, and a fake elliptic curve $E$ over $\mathbb{C}$ for $\Lambda,N$. Suppose given a $\mathbb{Z}$-lattice $\mathrm{latt}\subseteq\mathbb{C}^2$ and a bijection $e$ from the sections of $E.f$ over $\mathrm{id}_{\operatorname{Spec}\mathbb{C}}$ to $\mathbb{C}^2/\mathrm{latt}$ that carries the relative group law to addition, and which intertwines the action of each $x\in\Lambda$ on points with multiplication by the complexified matrix $\iota(x)$ on representatives. Let $m,\ell$ be nonzero naturals with $\ell\mid m$, let $P$ be a full level-$m$ structure on $E$, let $\tau$ lie in the upper half plane and $c\neq 0$ satisfy $c\cdot\mathrm{latt}=\iota$-period lattice of $\Lambda$ at $\tau$ (the image of $\Lambda$ under $x\mapsto\iota(x)\binom{\tau}{1}$), and let $w$ be a quaternion and $v_P$ a representative of $e(P.P)$ with $c\,v_P=m^{-1}\iota(w)\binom{\tau}{1}$. Let $L_0\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule and $t$ a quaternion such that, elementwise, $\Lambda t=\ell\Lambda+(\Lambda\cap L_0)w$. Finally let $K$ be an extra level structure at $\ell$ on $E$ whose points over every algebraically closed field $k$ with structure map $\mathbb{C}\to k$ are exactly those of the form $x\cdot\bigl((m/\ell)\,P.P\bigr)$ with $x\in\Lambda\cap L_0$ (here $m/\ell$ is natural division and $P.P$ is base changed along $\mathbb{C}\to k$). Then for every $v\in\mathbb{C}^2$, the point $e^{-1}([v])$ factors through the closed immersion cutting out $K$ if and only if there is $y\in\Lambda$ with $\iota(yt)\binom{\tau}{1}=(c\ell)\,v$.
--
--   This is the complex-analytic reading of an extra level structure at $\ell$ on a fake elliptic curve: through the uniformisation $e$ and the homothety $c$, such a $K$ is the subgroup $\frac{1}{c\ell}$ times the period lattice of a left ideal $\Lambda t$ of reduced norm $\ell$, modulo the period lattice of $\Lambda$. It is used in the construction of algebraic families with extra level over the analytic moduli description, in [`CerednikDrinfeld.QM.IsFineModuli.forall_exists_algebraicFamily_withExtraLevel_isPullback_smul_latt_eq_of_analytic`](thm.html#CerednikDrinfeld.QM.IsFineModuli.forall_exists_algebraicFamily_withExtraLevel_isPullback_smul_latt_eq_of_analytic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_factorsThrough_levK_symm_iff_exists_qmPeriodMap_mul_eq_of_forall_geomPoint.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField Pointwise
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.factorsThrough_levK_symm_iff_exists_qmPeriodMap_mul_eq_of_forall_geomPoint
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) {N : ℕ} (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ)
    (E : FakeEllipticCurve Λ N ℂ)

    (latt : Submodule ℤ (Fin 2 → ℂ))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f ≃ ((Fin 2 → ℂ) ⧸ latt.toAddSubgroup))
    (hE1 : ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f,
      e (E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e P + e Q)
    (hE2 : ∀ (x : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
      e P = (v : (Fin 2 → ℂ) ⧸ latt.toAddSubgroup) →
      e (pushPt (E.act x) (E.act_over x) P) =
        ((((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ latt.toAddSubgroup))

    (m ℓ : ℕ) (hm : m ≠ 0) (hℓ : ℓ ≠ 0) (hℓm : ℓ ∣ m) (P : E.FullLevel m)
    (τ : UpperHalfPlane) (c : ℂ) (hc : c ≠ 0) (hlatt : c • latt = qmPeriodLattice ι Λ τ)
    (w : ℍ[ℚ, a, b]) (vP : Fin 2 → ℂ) (hvP : e P.P = (vP : (Fin 2 → ℂ) ⧸ latt.toAddSubgroup))
    (hcvP : c • vP = ((m : ℂ)⁻¹) • qmPeriodMap ι τ w)

    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (t : ℍ[ℚ, a, b])
    (hLT : ∀ y : ℍ[ℚ, a, b], (∃ z ∈ Λ, z * t = y) ↔ ∃ z ∈ Λ, ∃ x ∈ Λ, x ∈ L₀ ∧ (ℓ : ℚ) • z + x * w = y)

    (K : E.ExtraLevel ℓ)
    (hK : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : ℂ →+* k) (Q : SchemeHomOver (geomPoint k sk) E.f),
      FactorsThrough K.levK Q ↔
        ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
          pushPt (E.act x) (E.act_over x)
            (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) = Q)
    (v : Fin 2 → ℂ) :
    FactorsThrough K.levK (e.symm (v : (Fin 2 → ℂ) ⧸ latt.toAddSubgroup)) ↔
      ∃ y ∈ Λ, qmPeriodMap ι τ (y * t) = (c * (ℓ : ℂ)) • v := by sorry
