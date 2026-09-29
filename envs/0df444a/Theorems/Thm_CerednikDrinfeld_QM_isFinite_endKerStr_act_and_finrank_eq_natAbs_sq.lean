-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_isFinite_endKerStr_act_and_finrank_eq_natAbs_sq
-- name    : CerednikDrinfeld.QM.isFinite_endKerStr_act_and_finrank_eq_natAbs_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/a1a3bfcb-0f1c-5fd2-a357-9feee63a48ca
-- title:
--   Kernel of quaternionic multiplication has rank n²
-- statement:
--   Let $K$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} K$ a morphism equipped with a relative group law $L$ on its functor of points (multiplication, unit and inverse on $T$-points $\{\varphi : T \to A \mid \varphi \circ f = t\}$, associative and unital with inverses, natural in $T$), assumed commutative, such that $f$ satisfies the bundle of properties: smooth, proper, with connected fibres and admitting a relative group law; and $f$ is smooth of relative dimension $2$. Let $q \neq q'$ be primes and $a, b \in \mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q}, a, b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $a > 0$ or $b > 0$, and for every height-one prime $v$ of the integers of $\mathbb{Q}$ the completion $\mathbb{H}[\mathbb{Q}, a, b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has every nonzero element invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q}, a, b]$ be a $\mathbb{Z}$-submodule that is an order and is maximal among orders containing it. Let $\mathrm{act} : \Lambda \to \operatorname{Hom}(A, A)$ send each $x$ to an endomorphism over $f$ which is a homomorphism for $L$ on $T$-points, with $\mathrm{act}(1) = \mathrm{id}_A$, $\mathrm{act}(xy) = \mathrm{act}(x) \circ \mathrm{act}(y)$, and $\mathrm{act}(x+y)$ equal on points to the $L$-product of $\mathrm{act}(x)$ and $\mathrm{act}(y)$. Let $c \in \Lambda$ be nonzero with $c + \bar{c} = t$ and $c\bar{c} = n$ for integers $t, n$. Then the fibre of $\mathrm{act}(c)$ over the unit section, namely the pullback of $\mathrm{act}(c)$ along $L.\mathrm{one}$ viewed over $\operatorname{Spec} K$ by the second projection, is finite, and its rank at the closed point of $\operatorname{Spec} K$ equals $|n|^2$.
--
--   This is the computation of the degree of a quaternionic multiplication on an abelian surface with an action of a maximal order in an indefinite quaternion algebra: the kernel of $\mathrm{act}(c)$ is a finite group scheme of order $\mathrm{nrd}(c)^2$. It is used to compute the rank of the geometric fibres attached to the quaternionic multiplication structure on a polarised abelian scheme, in the Čerednik–Drinfeld description of Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_isFinite_endKerStr_act_and_finrank_eq_natAbs_sq.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.isFinite_endKerStr_act_and_finrank_eq_natAbs_sq
    (K : Type) [Field K] [IsAlgClosed K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    [SmoothOfRelativeDimension 2 f]
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (act : ↥Λ → (A ⟶ A)) (act_over : ∀ x : ↥Λ, act x ≫ f = f)
    (act_hom : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
      pushPt (act x) (act_over x) (L.mul t P Q) = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q))
    (act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 A)
    (act_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x)
    (act_add : ∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver t f),
      pushPt (act (x + y)) (act_over (x + y)) P =
        L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P))
    (c : ↥Λ) (hc0 : (c : ℍ[ℚ, a, b]) ≠ 0)
    (t n : ℤ) (ht : (c : ℍ[ℚ, a, b]) + Star.star (c : ℍ[ℚ, a, b]) = ((t : ℚ) : ℍ[ℚ, a, b]))
    (hn : (c : ℍ[ℚ, a, b]) * Star.star (c : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b])) :
    IsFinite (L.endKerStr ⟨act c, act_over c⟩) ∧
      (L.endKerStr ⟨act c, act_over c⟩).finrank (IsLocalRing.closedPoint K) = n.natAbs ^ 2 := by sorry
