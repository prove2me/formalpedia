-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_pushPt_act_eq_nsmul_mul_pushPt_act_star_pushPt_act_of_eq_smul_one_add_star_mul
-- name    : CerednikDrinfeld.QM.pushPt_act_eq_nsmul_mul_pushPt_act_star_pushPt_act_of_eq_smul_one_add_star_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/ac46b060-6e1c-5591-a949-28dce09d89d1
-- title:
--   Action of c = 6(1 + b₀^⋆ b₀) on points
-- statement:
--   Let $K$ be a field, let $f : A \to \operatorname{Spec} K$ be a scheme over $K$ and let $L$ be a relative group law on $f$, i.e. a functorial group structure on the sets $\mathrm{SchemeHomOver}\,t\,f = \{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points for test morphisms $t : T \to \operatorname{Spec} K$. Let $\Lambda \subset \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order (an order in the sense of containing $1$, closed under multiplication, spanning the algebra over $\mathbb{Q}$ and finitely generated, and maximal among such), let $\star : \Lambda \to \Lambda$ be an arbitrary map, and let $\mathrm{act} : \Lambda \to (A \to A)$ assign to each $x \in \Lambda$ an endomorphism of $A$ over $\operatorname{Spec} K$ ($\mathrm{act}\,x$ followed by $f$ equals $f$). Assume: each $\mathrm{act}\,x$ induces a map on $T$-points (by post-composition, `pushPt`) compatible with the group law $L$; $\mathrm{act}\,1 = \mathrm{id}_A$; $\mathrm{act}(xy) = \mathrm{act}\,y$ followed by $\mathrm{act}\,x$ for $x,y \in \Lambda$ with $xy \in \Lambda$; and $\mathrm{act}(x+y)$ acts on each $T$-point $P$ as the $L$-product of the actions of $x$ and of $y$ on $P$. Let $b_0, c \in \Lambda$ with $c = 6\,(1 + (\star b_0)\,b_0)$ in $\mathbb{H}[\mathbb{Q},a,b]$. Then for every test morphism $t : T \to \operatorname{Spec} K$ and every $T$-point $x$, the point $\mathrm{act}\,c$ applied to $x$ equals the $(2\cdot 3)$-fold $L$-multiple of the $L$-product of $x$ with the image of $x$ under $\mathrm{act}\,b_0$ followed by $\mathrm{act}(\star b_0)$.
--
--   This is the pointwise dictionary entry translating the quaternionic element $c = 6(1 + b_0^\star b_0)$ of a maximal order into the group-law expression $6\,(x + b_0^\star b_0 x)$ on $T$-points of an abelian scheme with quaternionic multiplication. It is used in the computation of the geometric fibre $H^0$-rank of a tensor product pulled back along the endomorphism attached to $c$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_pushPt_act_eq_nsmul_mul_pushPt_act_star_pushPt_act_of_eq_smul_one_add_star_mul.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.pushPt_act_eq_nsmul_mul_pushPt_act_star_pushPt_act_of_eq_smul_one_add_star_mul
    (K : Type) [Field K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K)) (L : RelativeGroupLaw K f)
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (star : ↥Λ → ↥Λ)
    (act : ↥Λ → (A ⟶ A)) (act_over : ∀ x : ↥Λ, act x ≫ f = f)
    (act_hom : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
      pushPt (act x) (act_over x) (L.mul t P Q) = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q))
    (act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 A)
    (act_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x)
    (act_add : ∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver t f),
      pushPt (act (x + y)) (act_over (x + y)) P =
        L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P))
    (b0 c : ↥Λ) (hc : (c : ℍ[ℚ, a, b]) = (6 : ℚ) • (1 + (star b0 : ℍ[ℚ, a, b]) * (b0 : ℍ[ℚ, a, b]))) :
    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f),
      pushPt (act c) (act_over c) x =
        L.nsmul t (2 * 3) (L.mul t x (pushPt (act (star b0)) (act_over (star b0)) (pushPt (act b0) (act_over b0) x))) := by sorry
