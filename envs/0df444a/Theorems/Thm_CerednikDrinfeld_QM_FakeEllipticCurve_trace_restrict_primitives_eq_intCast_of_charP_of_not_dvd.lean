-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_trace_restrict_primitives_eq_intCast_of_charP_of_not_dvd
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.trace_restrict_primitives_eq_intCast_of_charP_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/ccc4a987-27ca-5dd6-823e-066d74ccc09b
-- title:
--   Trace on primitives of a pinned endomorphism when p∤ qq'
-- statement:
--   Fix distinct primes $q,q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`: $0<a$ or $0<b$, and for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule which is an order maximal among the orders containing it, let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, and let $\operatorname{star}:\Lambda\to\Lambda$ satisfy $\mu\,\operatorname{star}(x)=\bar{x}\mu$ for all $x$. Let $N$ be a natural number, $p$ a prime, $k$ an algebraically closed field of characteristic $p$, and $E$ a fake elliptic curve over $k$ for $\Lambda$ and level $N$: a scheme with structure morphism $f$ to $\operatorname{Spec} k$, a commutative relative group law $L$, the abelian-scheme property bundle (smooth, proper, connected fibres), all fibres of topological Krull dimension $2$, an action $\operatorname{act}$ of $\Lambda$ by endomorphisms over the base which is additive, unital, multiplicative and compatible with $L$ and satisfies the trace axiom on tangent vectors, together with the accompanying curve data. Let $H$ be a commutative ring which is a finite cocommutative Hopf $k$-algebra with $\dim_k H=p^{2\cdot 2}$ on which the $p$-th convolution power of the identity is the composite of the counit with the unit, and let $e$ be, for every commutative $k$-algebra $T$, a bijection from the convolution monoid of $k$-algebra maps $H\to T$ onto the set of $p$-torsion points of $L$ over $\operatorname{Spec} T$, carrying convolution products to $L$-products (`he_mul`) and natural in $T$ (`he_nat`); thus $H$ presents $E[p]$. Let $m\in\Lambda$ and let $\varphi_H$ be a $k$-algebra endomorphism of $H$ pinned to $m$, in the sense that for every commutative $k$-algebra $T$ and every point $q$, the point attached to $q\circ\varphi_H$ is $e_T(q)$ followed by $\operatorname{act}(m)$; assume $\varphi_H$ maps $\operatorname{primitives} k\,H=\ker(\Delta-(\cdot\otimes 1)-(1\otimes\cdot))$ into itself. Let $n\in\mathbb{Z}$ with $m+\bar{m}=n$ in $\mathbb{H}[\mathbb{Q},a,b]$, and assume $p\nmid qq'$. Then the trace of the restriction of $\varphi_H$ to the space of primitives equals the image of $n$ in $k$.
--
--   This is the Eichler–Shimura type trace identity for the action of a quaternionic endomorphism on the $p$-torsion of a fake elliptic curve, in the case of residue characteristic not dividing the discriminant $qq'$, where $E[p]$ is étale-like and $\Lambda\otimes\mathbb{F}_p$ is a matrix algebra. It feeds the statement `trace_restrict_primitives_eq_intCast_of_charP`, which removes the hypothesis $p\nmid qq'$, and the combined rank-and-trace statement for the space of primitives.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_trace_restrict_primitives_eq_intCast_of_charP_of_not_dvd.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.trace_restrict_primitives_eq_intCast_of_charP_of_not_dvd
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
    (hp : ¬ p ∣ q * q') :
    LinearMap.trace k ↥(primitives k H) (φH.toLinearMap.restrict hprim) = (n : k) := by sorry
