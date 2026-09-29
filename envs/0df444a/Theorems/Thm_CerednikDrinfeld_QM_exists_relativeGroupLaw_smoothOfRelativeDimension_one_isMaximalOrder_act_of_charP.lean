-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_relativeGroupLaw_smoothOfRelativeDimension_one_isMaximalOrder_act_of_charP
-- name    : CerednikDrinfeld.QM.exists_relativeGroupLaw_smoothOfRelativeDimension_one_isMaximalOrder_act_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/b4ace322-088d-50e6-86da-d3c0f0dc03d3
-- title:
--   Maximal quaternion order acting on a supersingular elliptic curve
-- statement:
--   Let $q$ be a prime and let $k$ be an algebraically closed field of characteristic $q$ that is algebraic over $\mathbb{F}_q$. Then there exist a scheme $A$, a morphism $f : A \to \operatorname{Spec} k$ and a relative group law $L$ on $f$, that is, a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$ of $T$-points over each $t : T \to \operatorname{Spec} k$, compatible with base change along morphisms $T' \to T$ over $\operatorname{Spec} k$, such that: $L$ is commutative on all such point sets; $f$ is smooth and proper with connected fibres and admits a relative group law; and $f$ is smooth of relative dimension $1$. Moreover there exist rationals $c, d$ with $c < 0$, $d < 0$ such that, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, the algebra $\mathbb{H}[\mathbb{Q},c,d] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra exactly when $q \in v$; a $\mathbb{Z}$-submodule $O \subseteq \mathbb{H}[\mathbb{Q},c,d]$ containing $1$, closed under multiplication, finitely generated and $\mathbb{Q}$-spanning the algebra, and maximal among such orders; and a map $\varepsilon : O \to (A \to A)$ with $\varepsilon(x)$ followed by $f$ equal to $f$ for all $x$, such that post-composition with $\varepsilon(x)$ is an endomorphism of the group law on every point set, $\varepsilon(1) = \mathrm{id}_A$, $\varepsilon(xy) = \varepsilon(y)$ followed by $\varepsilon(x)$ whenever $xy \in O$, and $\varepsilon(x+y)$ acts on points as the $L$-sum of the actions of $\varepsilon(x)$ and $\varepsilon(y)$.
--
--   This is the scheme-theoretic form of Deuring's theorem on supersingular elliptic curves: over an algebraic closure of $\mathbb{F}_q$ there is an elliptic curve, presented as an abelian scheme of relative dimension one with a commutative relative group law, whose endomorphisms realise a maximal order in the definite quaternion algebra over $\mathbb{Q}$ ramified exactly at $q$ and $\infty$. It supplies the fake elliptic curve used as a base point in the Cherednik–Drinfeld description of quaternionic Shimura curves at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_relativeGroupLaw_smoothOfRelativeDimension_one_isMaximalOrder_act_of_charP.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.exists_relativeGroupLaw_smoothOfRelativeDimension_one_isMaximalOrder_act_of_charP
    (q : ℕ) [Fact q.Prime]
    (k : Type) [Field k] [IsAlgClosed k] [CharP k q] [Algebra (ZMod q) k] [Algebra.IsAlgebraic (ZMod q) k] :
    ∃ (A : Scheme.{0}) (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f),
      L.IsCommutative ∧ AbelianSchemePropertyBundle k f ∧ SmoothOfRelativeDimension 1 f ∧
      ∃ (c d : ℚ) (_ : IsDefiniteRamifiedExactlyAt c d q)
        (O : Submodule ℤ ℍ[ℚ, c, d]) (_ : IsMaximalOrder O)
        (ε : ↥O → (A ⟶ A)) (hε : ∀ x : ↥O, ε x ≫ f = f),
        (∀ (x : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
          pushPt (ε x) (hε x) (L.mul t P Q) = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q)) ∧
        (∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, ε ⟨1, h⟩ = 𝟙 A) ∧
        (∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
          ε ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = ε y ≫ ε x) ∧
        (∀ (x y : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f),
          pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P)) := by sorry
