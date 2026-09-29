-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_trace_restrict_primitives_eq_intCast_of_charP_of_dvd
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.trace_restrict_primitives_eq_intCast_of_charP_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/63a30c40-5d36-565e-8810-a5920294376f
-- title:
--   Trace on primitives of E[p]: ramified case p ∣ qq'
-- statement:
--   Fix distinct primes $q,q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, let $\mu\in\Lambda$ satisfy $\mu^2=-qq'$, and let $\mathrm{star}:\Lambda\to\Lambda$ satisfy $\mu\cdot\mathrm{star}(x)=\bar x\mu$ for all $x\in\Lambda$. Let $N\in\mathbb{N}$, let $p$ be a prime, let $k$ be an algebraically closed field of characteristic $p$, and let $E$ be a `FakeEllipticCurve` for $\Lambda$, $N$ over $k$: a smooth proper scheme over $k$ with connected fibres of dimension $2$, a commutative relative group law $E.L$, and a $\Lambda$-action by endomorphisms $E.act$ compatible with the group law. Let $H$ be a finite-dimensional cocommutative Hopf algebra over $k$, commutative as a ring, with $\dim_k H=p^{4}$, whose $p$-fold convolution power of the identity is the composite of the counit with the unit, and let $e$ be a family, natural in $T$ and compatible with convolution and the group law, of bijections between the convolution monoid of $k$-algebra maps $H\to T$ and the $p$-torsion points of $E.L$ over $\mathrm{Spec}\,T$, for all commutative $k$-algebras $T$. Let $m\in\Lambda$ and let $\varphi_H:H\to H$ be a $k$-algebra endomorphism which under $e$ corresponds to following points by $E.act\ m$, and which maps the space of primitive elements $\ker(\Delta-(\cdot\otimes 1)-(1\otimes\cdot))$ of $H$ into itself. Let $n\in\mathbb{Z}$ with $m+\bar m=n$ in $\mathbb{H}[\mathbb{Q},a,b]$, and assume $p\mid qq'$. Then the trace over $k$ of the restriction of $\varphi_H$ to the primitives of $H$ equals the image of $n$ in $k$.
--
--   This is the Eichler–Shimura style trace identity for the action of the quaternion order on $\mathrm{Hom}(E[p],\mathbb{G}_a)$, in the case where the residue characteristic divides the discriminant $qq'$, so that the $p$-divisible group of the fake elliptic curve is the special formal $\mathcal{O}_D$-module of Drinfeld. It is the ramified half of the case split in [`CerednikDrinfeld.QM.FakeEllipticCurve.trace_restrict_primitives_eq_intCast_of_charP`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.trace_restrict_primitives_eq_intCast_of_charP), and is obtained from the identification of the primitives with a two-dimensional space attached to that formal module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_trace_restrict_primitives_eq_intCast_of_charP_of_dvd.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_Dieudonne_ModpRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra
  CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct

theorem CerednikDrinfeld.QM.FakeEllipticCurve.trace_restrict_primitives_eq_intCast_of_charP_of_dvd
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    {N : ℕ} {p : ℕ} [Fact p.Prime]
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (E : FakeEllipticCurve Λ N k)

    (H : Type) [CommRing H] [HopfAlgebra k H] [Module.Finite k H] [Coalgebra.IsCocomm k H]
    (hH : Module.finrank k H = p ^ (2 * 2))
    (hHp : PDivisibleGroup.Hopf.nsmulAlgHom k H p = (Algebra.ofId k H).comp (Bialgebra.counitAlgHom k H))
    (e : ∀ (T : Type) [CommRing T] [Algebra k T],
      WithConv (H →ₐ[k] T) ≃ E.L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap k T))) p)
    (he_mul : ∀ (T : Type) [CommRing T] [Algebra k T] (φ ψ : WithConv (H →ₐ[k] T)),
      ((e T (φ * ψ)).val : SchemeHomOver _ E.f) = E.L.mul _ (e T φ).val (e T ψ).val)
    (he_nat : ∀ (T T' : Type) [CommRing T] [Algebra k T] [CommRing T'] [Algebra k T']
        (g' : T →ₐ[k] T') (φ : WithConv (H →ₐ[k] T)),
      ((e T' (.toConv (g'.comp φ.ofConv))).val : SchemeHomOver _ E.f).1 =
        Spec.map (CommRingCat.ofHom g'.toRingHom) ≫ (e T φ).val.1)

    (m : ↥Λ) (φH : H →ₐ[k] H)
    (hφH : ∀ (T : Type) [CommRing T] [Algebra k T] (q : WithConv (H →ₐ[k] T)),
      ((e T (.toConv (q.ofConv.comp φH))).val : SchemeHomOver _ E.f).1 = (e T q).val.1 ≫ E.act m)
    (hprim : ∀ x ∈ primitives k H, φH x ∈ primitives k H)
    (n : ℤ) (hmn : (m : ℍ[ℚ, a, b]) + Star.star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]))
    (hp : p ∣ q * q') :
    LinearMap.trace k ↥(primitives k H) (φH.toLinearMap.restrict hprim) = (n : k) := by sorry
