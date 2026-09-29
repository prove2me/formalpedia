-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_of_forall_iso_tensorPow_tensor_le_one_of_rosatiCompatible_of_charZero
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.kernelTrivial_of_forall_iso_tensorPow_tensor_le_one_of_rosatiCompatible_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/e4d71640-db65-5807-9d04-e897ba9b4205
-- title:
--   Trivial kernel for ⋆-primitive Rosati-compatible bundles on fake elliptic curves
-- statement:
--   Fix distinct primes $q \ne q'$ and rationals $a,b$ such that the quaternion algebra $\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for each height-one prime $v$ of $\mathbb Q$ the completion $\mathbb H[\mathbb Q,a,b] \otimes_{\mathbb Q} \mathbb Q_v$ has all nonzero elements invertible exactly when $v$ divides $q$ or $q'$. Let $\Lambda$ be a $\mathbb Z$-submodule that is a maximal order (an order containing no strictly larger order), let $\mu \in \Lambda$ satisfy $\mu^2 = -(qq')\cdot 1$, and let $\mathrm{star} : \Lambda \to \Lambda$ satisfy $\mu\,\mathrm{star}(x) = \bar x\,\mu$ for all $x \in \Lambda$. Let $N \in \mathbb N$, let $k$ be an algebraically closed field of characteristic zero, and let $E$ be a fake elliptic curve of level $N$ over $k$ for $\Lambda$: a scheme $E.A$ with structure morphism $E.f$ to $\operatorname{Spec} k$, a commutative relative group law $E.L$, an abelian-scheme property bundle, two-dimensional fibres, and an action $E.\mathrm{act}$ of $\Lambda$ by endomorphisms over the base, together with the remaining data of the structure. Let $\mathcal L$ be a module on $E.A$ which is invertible (locally on $E.A$ its pullback is isomorphic to the unit module), assume the set of $k$-points lying in the translation stabiliser of $\mathcal L$, $\mathrm{kernelPts}\ E.f\ E.L\ \mathcal L$, is finite, and assume $\mathcal L$ is Rosati-compatible with the $\Lambda$-action through $\mathrm{star}$: for every $b \in \Lambda$ the pullbacks of the Mumford bundle $(\mathrm{add})^*\mathcal L \otimes \mathrm{pr}_1^*\mathcal L^\vee \otimes \mathrm{pr}_2^*\mathcal L^\vee$ along $(\mathrm{pr}_1, E.\mathrm{act}(b)\circ\mathrm{pr}_2)$ and along $(E.\mathrm{act}(\mathrm{star}\,b)\circ\mathrm{pr}_1, \mathrm{pr}_2)$ are isomorphic locally over $\operatorname{Spec} k$. Assume finally that $\mathcal L$ is $\star$-primitive: whenever $\mathcal M$ is invertible and Rosati-compatible in the same sense, $Q$ is invertible with all translations pulling it back to a module isomorphic to itself, and $\mathcal L \cong \mathcal M^{\otimes m} \otimes Q$ for some $m \in \mathbb N$, then $m \le 1$. The conclusion is `KernelTrivial E.f E.L 𝓛`: for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} k$ and every point $x$ of $E.A$ over $t$, if the pullback of the Mumford bundle along the slice at $x$ is isomorphic to the unit module locally over $\operatorname{Spec} R$, then $x$ is the identity section for $t$.
--
--   This is the statement that a $\star$-primitive Rosati-compatible invertible sheaf with finite kernel group of $k$-points on a fake elliptic curve in characteristic zero defines a principal polarisation, the kernel $K(\mathcal L)$ being trivial as a scheme rather than merely on $k$-points. It feeds the existence of a Rosati-compatible principal polarisation on fake elliptic curves over algebraically closed fields of characteristic zero, via [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_kernelTrivial_rosatiCompatible_of_isAlgClosed_of_charZero`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_kernelTrivial_rosatiCompatible_of_isAlgClosed_of_charZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_kernelTrivial_of_forall_iso_tensorPow_tensor_le_one_of_rosatiCompatible_of_charZero.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.kernelTrivial_of_forall_iso_tensorPow_tensor_le_one_of_rosatiCompatible_of_charZero
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (E : FakeEllipticCurve Λ N k)
    (𝓛 : E.A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (hK : (kernelPts E.f E.L 𝓛).Finite)
    (hR : RosatiCompatible E.f E.L 𝓛 E.act E.act_over star)
    (hprim : ∀ (𝓜 Q : E.A.Modules) (m : ℕ), Scheme.Modules.IsInvertible 𝓜 →
      RosatiCompatible E.f E.L 𝓜 E.act E.act_over star → InPicZero E.f E.L Q → Nonempty (𝓛 ≅ 𝓜.tensorPow m ⊗ Q) → m ≤ 1) :
    KernelTrivial E.f E.L 𝓛 := by sorry
