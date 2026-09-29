-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_act_trace_descend_of_isPullback_of_fg_of_isCommutative
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.act_trace_descend_of_isPullback_of_fg_of_isCommutative
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/5e43ec1f-4de0-5365-9b6c-1f14a2a2938a
-- title:
--   Descent of the trace condition along a cartesian square
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ that is a maximal order (an order not properly contained in any order), a natural number $N$, a commutative ring $L$, a fake elliptic curve $E$ of level data $(\Lambda,N)$ over $L$, and a $\mathbb{Z}$-subalgebra $R \subseteq L$ that is finitely generated. Suppose given a scheme $A_0$ with a morphism $f_0 : A_0 \to \operatorname{Spec} R$, a relative group law $L_0$ on $f_0$ (functorial group structure on sections $T \to A_0$ over $\operatorname{Spec} R$) which is commutative, the property bundle for $f_0$ (smooth, proper, connected fibres, a group law existing), and endomorphisms $\mathrm{act}_0(x) : A_0 \to A_0$ for $x \in \Lambda$, each over $\operatorname{Spec} R$, acting as group-law homomorphisms on $T$-points and additively in $x$. Suppose further $g : E.A \to A_0$ makes the square with $E.f$, $f_0$ and $\operatorname{Spec}(R \hookrightarrow L)$ cartesian, is compatible with the two group laws on points, and satisfies $E.\mathrm{act}(x) \,;\, g = g \,;\, \mathrm{act}_0(x)$ for all $x \in \Lambda$. The conclusion is the trace condition for $(f_0, L_0, \mathrm{act}_0)$: for every algebraically closed field $k$, every ring homomorphism $s_k : R \to k$, every finite-dimensional $k$-vector space $V$ and every injective $\tau : V \to \{$sections over the dual-number base point $\operatorname{tangentBase}\ k\ s_k\}$ whose image is exactly the set of tangent vectors (those whose restriction along the zero section is the identity section), additive for $L_0$ and compatible with $k$-scaling via $\operatorname{tangentScale}$, and for every $x \in \Lambda$, every $k$-linear $\Phi : V \to V$ with $\tau(\Phi v) = \mathrm{act}_0(x) \circ \tau(v)$, and every integer $nn$ with $x + \bar{x} = nn$ in $\mathbb{H}[\mathbb{Q},a,b]$, one has $\operatorname{tr}_k(\Phi) = nn$ in $k$.
--
--   This is the descent, to the base $\operatorname{Spec} R$, of the trace condition on the action of the quaternion order on the Lie algebra at geometric points — the field `act_trace` in the definition of a fake elliptic curve — from the fibre $E$ over $L$ along a cartesian square. It is used in the construction of a finitely generated stage over which a fake elliptic curve with its level structure spreads out.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_act_trace_descend_of_isPullback_of_fg_of_isCommutative.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.act_trace_descend_of_isPullback_of_fg_of_isCommutative
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ)
    (L : Type) [CommRing L] (E : FakeEllipticCurve Λ N L)
    (R : Subalgebra ℤ L) (hR : R.FG)
    (A₀ : Scheme.{0}) (f₀ : A₀ ⟶ Spec (CommRingCat.of ↥R)) (L₀ : RelativeGroupLaw ↥R f₀)
    (hcomm₀ : L₀.IsCommutative) (hbundle₀ : AbelianSchemePropertyBundle ↥R f₀)
    (act₀ : ↥Λ → (A₀ ⟶ A₀)) (hact_over₀ : ∀ x : ↥Λ, act₀ x ≫ f₀ = f₀)
    (hact_hom₀ : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (P Q : SchemeHomOver t f₀),
      pushPt (act₀ x) (hact_over₀ x) (L₀.mul t P Q) = L₀.mul t (pushPt (act₀ x) (hact_over₀ x) P) (pushPt (act₀ x) (hact_over₀ x) Q))
    (hact_add₀ : ∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (P : SchemeHomOver t f₀),
      pushPt (act₀ (x + y)) (hact_over₀ (x + y)) P =
        L₀.mul t (pushPt (act₀ x) (hact_over₀ x) P) (pushPt (act₀ y) (hact_over₀ y) P))
    (g : E.A ⟶ A₀) (hg : CategoryTheory.IsPullback g E.f f₀ (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
    (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ g =
        (L₀.mul (t' ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (hact : ∀ x : ↥Λ, E.act x ≫ g = g ≫ act₀ x) :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : ↥R →+* k)
      (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f₀),
      Function.Injective τ →
      (∀ P : SchemeHomOver (tangentBase k sk) f₀, P ∈ Set.range τ ↔ IsTangentVector L₀ k sk P) →
      (∀ v w : V, τ (v + w) = L₀.mul (tangentBase k sk) (τ v) (τ w)) →
      (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
      ∀ (x : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (act₀ x) (hact_over₀ x) (τ v)) →
      ∀ nn : ℤ, (x : ℍ[ℚ, a, b]) + star (x : ℍ[ℚ, a, b]) = ((nn : ℚ) : ℍ[ℚ, a, b]) →
        LinearMap.trace k V Φ = (nn : k) := by sorry
