-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_forall_trace_eq_apply_of_isLocalRing_of_smooth_of_isCommutative
-- name    : CerednikDrinfeld.QM.exists_forall_trace_eq_apply_of_isLocalRing_of_smooth_of_isCommutative
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/43cc4cad-25dc-5c94-8cc5-ce813f119c26
-- title:
--   Trace of a lattice action over a local base
-- statement:
--   Let $a,b$ be rationals and $\Lambda$ a $\mathbb{Z}$-submodule of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$. Let $R$ be a commutative local ring, $A$ a scheme and $f : A \to \operatorname{Spec} R$, equipped with a `RelativeGroupLaw` $L$ for $f$: functorial multiplication, unit and inverse operations on the sets $\mathrm{SchemeHomOver}\ t\ f$ of morphisms $T \to A$ over a given $t : T \to \operatorname{Spec} R$, satisfying associativity, the unit laws, left inversion, and compatibility with base change along $\psi : T' \to T$ over $\operatorname{Spec} R$. Assume $L$ is commutative, $f$ is smooth, and that $\mathrm{act}$ assigns to each $x \in \Lambda$ an endomorphism $\mathrm{act}\ x$ of $A$ with $\mathrm{act}\ x$ followed by $f$ equal to $f$, such that post-composition with $\mathrm{act}\ x$ is multiplicative for $L$ on $T$-points, for every $T \to \operatorname{Spec} R$. Then there is a function $t : \Lambda \to R$ with the following property. Let $k$ be a field, $sk : R \to k$ a ring homomorphism, $x \in \Lambda$, $V$ a $k$-vector space and $\tau : V \to \mathrm{SchemeHomOver}(\mathrm{tangentBase}\ k\ sk)\ f$ an injection whose image is exactly the set of points $P$ over $\operatorname{Spec} k[\varepsilon]$ with $\mathrm{tangentZero}\ k$ followed by $P$ equal to the unit section over $\mathrm{geomPoint}\ k\ sk$, such that $\tau(v+w) = L.\mathrm{mul}\ (\tau v)\ (\tau w)$ and $\tau(c \cdot v)$ is $\mathrm{tangentScale}\ k\ c$ followed by $\tau v$. Then every $k$-linear $\Phi : V \to V$ with $\tau(\Phi v) = \tau(v)$ followed by $\mathrm{act}\ x$ for all $v$ satisfies $\operatorname{tr}_k \Phi = sk(t\,x)$.
--
--   This is the local-base form of the statement that the traces of the differentials of a lattice action on a smooth commutative relative group scheme are given by a single $R$-valued function on the lattice, independent of the chosen residue field, point and tangent-space identification. It feeds into the trace computation for the fake elliptic curves occurring in the Čerednik–Drinfeld uniformisation, being used by [`CerednikDrinfeld.QM.FakeEllipticCurve.trace_eq_of_tower_of_forall_isPullback_of_isCommutative_of_smoothOfRelativeDimension`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.trace_eq_of_tower_of_forall_isPullback_of_isCommutative_of_smoothOfRelativeDimension).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_forall_trace_eq_apply_of_isLocalRing_of_smooth_of_isCommutative.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.exists_forall_trace_eq_apply_of_isLocalRing_of_smooth_of_isCommutative
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    {R : Type u} [CommRing R] [IsLocalRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hL : L.IsCommutative) (hf : Smooth f)
    (act : ↥Λ → (A ⟶ A)) (act_over : ∀ x : ↥Λ, act x ≫ f = f)
    (act_hom : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt (act x) (act_over x) (L.mul t P Q) = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q)) :
    ∃ t : ↥Λ → R,
      ∀ (k : Type u) [Field k] (sk : R →+* k) (x : ↥Λ)
        (V : Type u) [AddCommGroup V] [Module k V] (τ : V → SchemeHomOver (tangentBase k sk) f),
        Function.Injective τ →
        (∀ P : SchemeHomOver (tangentBase k sk) f, P ∈ Set.range τ ↔ IsTangentVector L k sk P) →
        (∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w)) →
        (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
        ∀ Φ : V →ₗ[k] V, (∀ v : V, τ (Φ v) = pushPt (act x) (act_over x) (τ v)) →
          LinearMap.trace k V Φ = sk (t x) := by sorry
