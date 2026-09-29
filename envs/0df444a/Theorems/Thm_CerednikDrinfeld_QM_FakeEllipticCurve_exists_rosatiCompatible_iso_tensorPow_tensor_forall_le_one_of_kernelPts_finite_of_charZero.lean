-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_rosatiCompatible_iso_tensorPow_tensor_forall_le_one_of_kernelPts_finite_of_charZero
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_rosatiCompatible_iso_tensorPow_tensor_forall_le_one_of_kernelPts_finite_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/ffee9308-bf56-5b75-9aa0-fbe99d7afacb
-- title:
--   Rosati-compatible sheaves are powers of a ⋆-primitive one
-- statement:
--   Fix primes $q\neq q'$ and rationals $a,b$ such that the quaternion algebra $\mathbb H[\mathbb Q,a,b]$ is indefinite ($0<a$ or $0<b$) and, for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$, the completion $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a division algebra exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb Z$-submodule of $\mathbb H[\mathbb Q,a,b]$ that is an order maximal among orders, let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, and let $\mathrm{star}:\Lambda\to\Lambda$ be a map with $\mu\,\mathrm{star}(x)=\bar x\,\mu$ for all $x$. Let $N$ be a natural number, $k$ an algebraically closed field of characteristic $0$, and $E$ a term of the project's structure `FakeEllipticCurve Λ N k`: a scheme `E.A` over $\mathrm{Spec}\,k$ with a commutative relative group law `E.L`, abelian-scheme property bundle, two-dimensional fibres, and an action `E.act` of $\Lambda$ by endomorphisms over the base. Let $\mathcal L$ be a module on `E.A` that is invertible (each point has a neighbourhood on which $\mathcal L$ pulls back to the unit), whose kernel points — those $k$-sections of `E.f` lying in the stabiliser of $\mathcal L$ for translation by `E.L` — form a finite set, and which is Rosati-compatible for `E.act` and $\mathrm{star}$, meaning that for every $b\in\Lambda$ the two pullbacks of the Mumford bundle of $\mathcal L$ along $(\mathrm{pr}_1,\ \mathrm{act}(b)\circ\mathrm{pr}_2)$ and $(\mathrm{act}(\mathrm{star}\,b)\circ\mathrm{pr}_1,\ \mathrm{pr}_2)$ are isomorphic locally on the base. The conclusion asserts the existence of modules $\mathcal L_g,P$ on `E.A` and a natural number $n$ such that $\mathcal L_g$ is invertible with finitely many kernel points and Rosati-compatible in the same sense, $P$ is invertible with $T_x^\ast P\cong P$ for every $k$-section $x$ (the project's `InPicZero`), $n>0$, there is an isomorphism $\mathcal L\cong \mathcal L_g^{\otimes n}\otimes P$ (with $\mathcal L_g^{\otimes n}$ the iterated tensor power, the unit object for $n=0$), and $\mathcal L_g$ is $\star$-primitive: whenever $\mathcal M$ is invertible and Rosati-compatible, $Q$ is in $\mathrm{Pic}^0$ in the above sense, $m$ is a natural number and $\mathcal L_g\cong\mathcal M^{\otimes m}\otimes Q$, then $m\le 1$.
--
--   This is the division step for non-degenerate Rosati-compatible line bundles on a fake elliptic curve over an algebraically closed field of characteristic zero: every such bundle is, modulo $\mathrm{Pic}^0$, a positive tensor power of one that admits no further such division. It feeds the construction of a Rosati-compatible bundle with trivial kernel of points on a fake elliptic curve, used in normalising the polarisation data in the Čerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_rosatiCompatible_iso_tensorPow_tensor_forall_le_one_of_kernelPts_finite_of_charZero.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_rosatiCompatible_iso_tensorPow_tensor_forall_le_one_of_kernelPts_finite_of_charZero
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (E : FakeEllipticCurve Λ N k)
    (𝓛 : E.A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (hK : (kernelPts E.f E.L 𝓛).Finite)
    (hR : RosatiCompatible E.f E.L 𝓛 E.act E.act_over star) :
    ∃ (𝓛g P : E.A.Modules) (n : ℕ), Scheme.Modules.IsInvertible 𝓛g ∧ (kernelPts E.f E.L 𝓛g).Finite ∧
      RosatiCompatible E.f E.L 𝓛g E.act E.act_over star ∧ InPicZero E.f E.L P ∧ 0 < n ∧
      Nonempty (𝓛 ≅ 𝓛g.tensorPow n ⊗ P) ∧
      ∀ (𝓜 Q : E.A.Modules) (m : ℕ), Scheme.Modules.IsInvertible 𝓜 → RosatiCompatible E.f E.L 𝓜 E.act E.act_over star →
        InPicZero E.f E.L Q → Nonempty (𝓛g ≅ 𝓜.tensorPow m ⊗ Q) → m ≤ 1 := by sorry
