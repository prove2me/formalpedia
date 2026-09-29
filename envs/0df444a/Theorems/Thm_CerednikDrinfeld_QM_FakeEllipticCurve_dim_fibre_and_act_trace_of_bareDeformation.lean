-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_dim_fibre_and_act_trace_of_bareDeformation
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.dim_fibre_and_act_trace_of_bareDeformation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/025115ed-ce25-509d-b386-b17906345bbe
-- title:
--   Fibre dimension and trace condition pass to a bare deformation
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and a natural number $N$. Let $B$ and $B_0$ be commutative rings with $B_0$ a $B$-algebra such that $B \to B_0$ is surjective with nilpotent kernel, let $E_0$ be a fake elliptic curve of type $(\Lambda,N)$ over $B_0$, and let $D$ be a bare deformation of the pair $(E_0.f, E_0.L)$ over $B$: a scheme $D.A$ with a morphism $D.f : D.A \to \operatorname{Spec} B$, a commutative relative group law $D.L$, an abelian-scheme property bundle, and a morphism $g : E_0.A \to D.A$ making the square over $\operatorname{Spec} B_0 \to \operatorname{Spec} B$ cartesian and compatible with the two group laws. Assume given endomorphisms $\mathrm{act}(x) : D.A \to D.A$ for $x \in \Lambda$, each commuting with $D.f$, such that $g$ is equivariant: $E_0.\mathrm{act}(x)$ followed by $g$ equals $g$ followed by $\mathrm{act}(x)$. The conclusion is the conjunction of two assertions. First, for every point $s$ of $\operatorname{Spec} B$ the topological Krull dimension of the set-theoretic fibre $D.f^{-1}(s)$ is $2$. Second, the trace condition holds: for every algebraically closed field $k$, every ring homomorphism $sk : B \to k$, every finite-dimensional $k$-vector space $V$ and every map $\tau$ from $V$ to morphisms $\operatorname{Spec} k[\varepsilon] \to D.A$ lying over the base morphism $\operatorname{Spec} k[\varepsilon] \to \operatorname{Spec} B$ induced by $sk$, such that $\tau$ is injective, its image consists exactly of those $P$ with $\mathrm{tangentZero}\,k$ followed by $P$ equal to the identity section at the geometric point $sk$, $\tau$ carries addition to multiplication under $D.L$, and $\tau(c \cdot v)$ is $\mathrm{tangentScale}\,k\,c$ followed by $\tau(v)$; then for every $m \in \Lambda$, every $k$-linear $\Phi : V \to V$ with $\tau(\Phi v)$ equal to $\tau(v)$ followed by $\mathrm{act}(m)$, and every integer $n$ with $m + \bar m = n$ in $\mathbb{H}[\mathbb{Q},a,b]$, one has $\operatorname{tr}_k \Phi = n$ in $k$.
--
--   These are exactly the `dim_fibre` and `act_trace` fields of `FakeEllipticCurve` for the deformed data $(D.A, D.f, D.L, \mathrm{act})$, namely relative dimension $2$ and Drinfeld's reduced-trace condition on the action of $\Lambda$ on the tangent space at the origin of a geometric fibre. The statement is used in assembling a fake elliptic curve over $B$ from a bare deformation of one over $B_0$, and is cited by the results producing pullback structures for such deformations, including the Artinian and full-level variants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_dim_fibre_and_act_trace_of_bareDeformation.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.dim_fibre_and_act_trace_of_bareDeformation
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (B B₀ : Type) [CommRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₀)))
    (E₀ : FakeEllipticCurve Λ N B₀) (D : BareDeformation E₀.f E₀.L B)
    (act : ↥Λ → (D.A ⟶ D.A)) (act_over : ∀ x : ↥Λ, act x ≫ D.f = D.f)
    (hact : ∀ x : ↥Λ, E₀.act x ≫ D.g = D.g ≫ act x) :
    (∀ s : ↥(Spec (CommRingCat.of B)), topologicalKrullDim ↥(D.f.base ⁻¹' {s}) = 2) ∧
    (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : B →+* k)
      (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) D.f),
      Function.Injective τ →
      (∀ P : SchemeHomOver (tangentBase k sk) D.f, P ∈ Set.range τ ↔ IsTangentVector D.L k sk P) →
      (∀ v w : V, τ (v + w) = D.L.mul (tangentBase k sk) (τ v) (τ w)) →
      (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
      ∀ (m : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (act m) (act_over m) (τ v)) →
      ∀ n : ℤ, (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
        LinearMap.trace k V Φ = (n : k)) := by sorry
