-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_injective_range_isTangentVector_of_isFormalCoordinates
-- name    : CerednikDrinfeld.QM.exists_injective_range_isTangentVector_of_isFormalCoordinates
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/9094182d-4208-5eba-a0cc-450d038da74b
-- title:
--   Formal coordinates parametrise the tangent space at the origin
-- statement:
--   Let $B$ be a commutative ring, $f : A \to \operatorname{Spec} B$ a scheme over $B$, $g$ a natural number, $L$ a relative group law on $f$ over $B$ (functorial multiplication, unit and inverse on the sets $\{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$ for bases $t : T \to \operatorname{Spec} B$, satisfying the group axioms and compatible with base change), $F$ a $g$-dimensional multivariate formal group law over $B$, and $\theta$ an assignment sending each $B$-algebra $B'$ and each tuple in $(B')^g$ to a point of $A$ over $\operatorname{Spec} B' \to \operatorname{Spec} B$. Assume $\theta$ is a system of formal coordinates for $L$ and $F$: it is natural in $B$-algebra maps on tuples of nilpotents, and for every $B$-algebra $B'$ and ideal $J$ with $J^{n+1} = 0$ the tuples with entries in $J$ are carried bijectively onto those points whose reduction modulo $J$ is the unit section, with $\theta$ of the $n$-truncated $F$-sum of two such tuples equal to the $L$-product of their images. Let $k$ be a field with a $B$-algebra structure. Then there is a map $\tau$ from $k^g$ to the points of $A$ over $\operatorname{Spec} k[\varepsilon] \to \operatorname{Spec} B$ induced by $B \to k \to k[\varepsilon]$, such that: $\tau(v)$ has the same underlying morphism as $\theta_{k[\varepsilon]}(\varepsilon v_1,\dots,\varepsilon v_g)$; $\tau$ is injective; the image of $\tau$ consists exactly of those points $P$ with $\varepsilon \mapsto 0$ composed with $P$ equal to the unit section at the $k$-point of $\operatorname{Spec} B$; $\tau(v+w) = L.\mathrm{mul}\,(\tau v)(\tau w)$; and for $c \in k$ the morphism underlying $\tau(c \cdot v)$ is the scaling $\varepsilon \mapsto c\varepsilon$ of $k[\varepsilon]$ followed by the morphism underlying $\tau(v)$.
--
--   This is the dictionary identifying the Lie algebra $k^g$ of the formal group $F$ with the tangent space at the origin of the fibre of $A$ at $B \to k$, as an additive and $k$-homogeneous bijection onto the $k[\varepsilon]$-points that reduce to the unit section. It is used in the theory of fake elliptic curves, where Drinfeld's trace condition on the tangent space at the origin is formulated for any $k$-module mapped onto the tangent vectors in this way; results on formal modules and formal completions along the unit section cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_injective_range_isTangentVector_of_isFormalCoordinates.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.exists_injective_range_isTangentVector_of_isFormalCoordinates
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} {g : ℕ}
    (L : RelativeGroupLaw B f) (F : MvFormalGroup g B) (θ : RelativeGroupLaw.FormalCoordinates f g)
    (hθ : L.IsFormalCoordinates F θ) (k : Type) [Field k] [Algebra B k] :
    ∃ τ : (Fin g → k) → SchemeHomOver (tangentBase k (algebraMap B k)) f,
      (∀ v, (τ v).1 = (θ (DualNumber k) (fun i => TrivSqZeroExt.inr (v i))).1) ∧
      Function.Injective τ ∧
      (∀ P, P ∈ Set.range τ ↔ IsTangentVector L k (algebraMap B k) P) ∧
      (∀ v w, τ (v + w) = L.mul (tangentBase k (algebraMap B k)) (τ v) (τ w)) ∧
      (∀ (c : k) (v : Fin g → k), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) := by sorry
