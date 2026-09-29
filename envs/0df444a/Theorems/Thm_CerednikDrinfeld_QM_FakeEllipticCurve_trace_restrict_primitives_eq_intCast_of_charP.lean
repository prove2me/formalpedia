-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_trace_restrict_primitives_eq_intCast_of_charP
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.trace_restrict_primitives_eq_intCast_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/6ef63a5a-7bc1-5b84-b1a3-cb16feb7d9a2
-- title:
--   Trace on primitives of E[p] equals the reduced trace
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$ and let $a,b\in\mathbb Q$ be such that the quaternion algebra $\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`: $0<a$ or $0<b$, and for each height-one prime $v$ of $\mathcal O_{\mathbb Q}$ every nonzero element of $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule which is an order maximal among orders containing it, let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, and let $\mathrm{star}:\Lambda\to\Lambda$ satisfy $\mu\,\mathrm{star}(x)=\bar x\,\mu$ for all $x\in\Lambda$. Let $p$ be a prime, $k$ an algebraically closed field of characteristic $p$, $N$ a natural number, and $E$ a fake elliptic curve of type $(\Lambda,N)$ over $k$, i.e. a scheme $E.A$ over $\operatorname{Spec} k$ carrying a commutative relative group law $E.L$, an abelian-scheme property bundle, fibres of topological Krull dimension $2$, an action $E.\mathrm{act}$ of $\Lambda$ by endomorphisms over the base which is additive and multiplicative on points and satisfies the trace axiom for tangent spaces, together with its further curve data. Let $H$ be a finite cocommutative commutative Hopf $k$-algebra with $\dim_k H=p^{2\cdot 2}$ on which multiplication by $p$ (in the convolution sense) is $\eta\circ\varepsilon$, and let $e$ be a family of bijections, for every commutative $k$-algebra $T$, from $\operatorname{Hom}_{k\text{-alg}}(H,T)$ with its convolution monoid structure onto the set of $T$-points of $E$ killed by $p$ under $E.L$, compatible with multiplication and natural in $T$. Let $m\in\Lambda$ and let $\varphi^\sharp:H\to H$ be a $k$-algebra endomorphism which, through $e$, induces composition with $E.\mathrm{act}\,m$ on all these point sets, and which maps the primitives of $H$ (the kernel of $\Delta-1\otimes\mathrm{id}-\mathrm{id}\otimes 1$) into themselves. Then for any integer $n$ with $m+\bar m=n$ in $\mathbb H[\mathbb Q,a,b]$, the trace of the restriction of $\varphi^\sharp$ to the primitives of $H$ equals the image of $n$ in $k$.
--
--   This is the speciality, or trace, statement for the action of a maximal quaternion order on a fake elliptic curve in characteristic $p$, transferred from coherent cohomology to the Hopf algebra of the $p$-torsion group scheme, where the primitives play the role of $\operatorname{Hom}(E[p],\mathbb G_a)$. It is used in the companion result computing both the dimension of the primitives and this trace, a step in the analysis of fake elliptic curves over fields of characteristic $p$ underlying the Čerednik–Drinfeld description of Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_trace_restrict_primitives_eq_intCast_of_charP.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.trace_restrict_primitives_eq_intCast_of_charP
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
    (n : ℤ) (hmn : (m : ℍ[ℚ, a, b]) + Star.star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b])) :
    LinearMap.trace k ↥(primitives k H) (φH.toLinearMap.restrict hprim) = (n : k) := by sorry
