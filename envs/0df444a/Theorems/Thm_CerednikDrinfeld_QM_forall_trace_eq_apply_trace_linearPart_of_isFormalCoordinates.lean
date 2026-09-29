-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_forall_trace_eq_apply_trace_linearPart_of_isFormalCoordinates
-- name    : CerednikDrinfeld.QM.forall_trace_eq_apply_trace_linearPart_of_isFormalCoordinates
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/ff467c44-b0c0-560f-b798-9f78d3e7fcfe
-- title:
--   Trace of an endomorphism equals the trace of its linear part
-- statement:
--   Let $B$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} B$, let $L$ be a relative group law on $f$ (functorial multiplication, unit and inverse on points of $A$ over a base, with associativity, unit and inverse laws and compatibility with base change), let $F$ be a $g$-dimensional formal group law over $B$, and let $\theta$ assign to each $B$-algebra $B'$ and each tuple $s \in (B')^g$ a morphism $\operatorname{Spec} B' \to A$ over $\operatorname{Spec} B$. Assume $\theta$ is a system of formal coordinates for $L$ and $F$: it commutes with $B$-algebra maps on nilpotent tuples, and for every $B'$ and ideal $J$ with $J^{n+1} = 0$, the points $\theta_{B'}(s)$ for $s$ with entries in $J$ reduce to the unit modulo $J$, depend injectively on $s$, exhaust the points that reduce to the unit modulo $J$, and satisfy $\theta_{B'}(F.\mathrm{nilMul}\,n\,s\,t) = L.\mathrm{mul}(\theta_{B'}(s), \theta_{B'}(t))$. Let $a : A \to A$ satisfy $a \circ f = f$ in the sense $a \mathbin{\text{followed by}} f = f$, and let $\varphi : \mathrm{Fin}\,g \to B[[x_1,\dots,x_g]]$ have zero constant coefficients and represent $a$ in these coordinates: for every $B$-algebra $B'$, every ideal $J$ with $J^{n+1} = 0$ and every tuple $s$ with entries in $J$, the point $\theta_{B'}$ of the tuple of truncated evaluations $\mathrm{nilEval}\,n\,(\varphi_i)\,s$ equals $\theta_{B'}(s)$ post-composed with $a$. The conclusion asserts: for every field $k$, every ring homomorphism $s_k : B \to k$, every finite-dimensional $k$-vector space $V$ and every map $\tau$ from $V$ to the morphisms $\operatorname{Spec} k[\varepsilon] \to A$ lying over the structure map $\operatorname{Spec} k[\varepsilon] \to \operatorname{Spec} B$ induced by $s_k$, such that $\tau$ is injective, its range is exactly the tangent vectors for $L$ at $s_k$ (those points whose restriction along $\varepsilon \mapsto 0$ is the unit of $L$ at the geometric point), $\tau(v+w) = L.\mathrm{mul}(\tau v, \tau w)$, and $\tau(c \cdot v)$ is $\tau(v)$ precomposed with the scaling $\varepsilon \mapsto c\varepsilon$; then for every $k$-linear $\Phi : V \to V$ with $\tau(\Phi v)$ equal to $\tau(v)$ post-composed with $a$ for all $v$, one has $\operatorname{tr}_k(\Phi) = s_k(\operatorname{tr} \mathrm{linearPart}\,\varphi)$, where $\mathrm{linearPart}\,\varphi \in M_g(B)$ is the matrix of coefficients of the degree-one monomials of the $\varphi_i$.
--
--   This is the statement that the trace of the induced action of an endomorphism on the tangent space at the identity is computed by the trace of the Jacobian matrix at the origin of the power series representing it in formal coordinates, stated for an arbitrary tangent presentation $(V,\tau)$ rather than the standard one $k^g$. It is used in the computation of traces of Hecke or quaternionic correspondences acting on tangent spaces, via [`CerednikDrinfeld.QM.forall_trace_eq_intCast_of_isFormalCoordinates_of_isSpecial`](thm.html#CerednikDrinfeld.QM.forall_trace_eq_intCast_of_isFormalCoordinates_of_isSpecial), and rests on the existence of the standard presentation supplied by [`CerednikDrinfeld.QM.exists_injective_range_isTangentVector_of_isFormalCoordinates`](thm.html#CerednikDrinfeld.QM.exists_injective_range_isTangentVector_of_isFormalCoordinates).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_forall_trace_eq_apply_trace_linearPart_of_isFormalCoordinates.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.forall_trace_eq_apply_trace_linearPart_of_isFormalCoordinates
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} {g : ℕ}
    (L : RelativeGroupLaw B f) (F : MvFormalGroup g B) (θ : RelativeGroupLaw.FormalCoordinates f g)
    (hθ : L.IsFormalCoordinates F θ)
    (a : A ⟶ A) (ha : a ≫ f = f)

    (φ : Fin g → MvPowerSeries (Fin g) B) (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφ : ∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ s : Fin g → B', (∀ i, s i ∈ J) →
        θ B' (fun i => MvFormalGroup.nilEval n (φ i) s) = pushPt a ha (θ B' s)) :
    ∀ (k : Type) [Field k] (sk : B →+* k)
      (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f),
      Function.Injective τ →
      (∀ P : SchemeHomOver (tangentBase k sk) f, P ∈ Set.range τ ↔ IsTangentVector L k sk P) →
      (∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w)) →
      (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
      ∀ Φ : V →ₗ[k] V, (∀ v : V, τ (Φ v) = pushPt a ha (τ v)) →
        LinearMap.trace k V Φ = sk (Matrix.trace (MvFormalGroup.linearPart φ)) := by sorry
