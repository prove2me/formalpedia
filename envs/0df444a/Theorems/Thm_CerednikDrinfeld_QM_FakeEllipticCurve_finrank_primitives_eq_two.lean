-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_finrank_primitives_eq_two
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.finrank_primitives_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/8b03f43f-1e59-5aee-bfe4-d780150d93ab
-- title:
--   Primitives of the p-torsion Hopf algebra have rank 2
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$ and let $a,b\in\mathbb{Q}$ be such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order (it contains $1$, is closed under multiplication, $\mathbb{Q}$-spans the algebra and is finitely generated, and is maximal among such), let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, and let $\mathrm{star}:\Lambda\to\Lambda$ satisfy $\mu\,\mathrm{star}(x)=\bar{x}\mu$ for all $x\in\Lambda$. Let $N\in\mathbb{N}$, let $p$ be a prime, let $k$ be an algebraically closed field of characteristic $p$, and let $E$ be a fake elliptic curve of type $(\Lambda,N)$ over $k$: a scheme $A$ with a morphism $f$ to $\operatorname{Spec} k$ carrying a commutative relative group law $L$, satisfying the abelian-scheme property bundle (smooth, proper, connected fibres, group law present), all fibres of topological Krull dimension $2$, together with an action of $\Lambda$ by endomorphisms over $f$ compatible with the group law and satisfying the trace condition on tangent spaces, and the remaining data of the structure. Let $H$ be a commutative ring which is a finite, cocommutative Hopf algebra over $k$ with $\operatorname{rank}_k H=p^{2\cdot 2}$, such that the $p$-th convolution power of the identity of $H$ equals the composite of the counit with the structure map $k\to H$. Assume given, for every commutative $k$-algebra $T$, an equivalence $e_T$ between the convolution monoid $\mathrm{WithConv}(H\to_{\mathrm{alg}} T)$ and the set of $T$-points of $A$ over $k$ killed by $p$ for $L$, which is multiplicative (the convolution product corresponds to $L.\mathrm{mul}$) and natural in $T$ under base change along $k$-algebra maps. Then the space of primitive elements of $H$, the kernel of $x\mapsto \Delta(x)-x\otimes 1-1\otimes x$, has $k$-dimension $2$.
--
--   For a fake elliptic curve $E$ over an algebraically closed field of characteristic $p$, the primitives of the Hopf algebra of $E[p]$ are the additive characters $\operatorname{Hom}(E[p],\mathbb{G}_a)$, and the statement identifies their dimension with the dimension $2$ of the abelian surface, equivalently with $\dim_k H^1(E,\mathcal{O}_E)$. It is used in the computation of traces of the $\Lambda$-action on primitives, in the analysis of the mod $p$ Dieudonné realisation entering the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_finrank_primitives_eq_two.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.finrank_primitives_eq_two
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
        Spec.map (CommRingCat.ofHom g'.toRingHom) ≫ (e T φ).val.1) :
    Module.finrank k ↥(primitives k H) = 2 := by sorry
