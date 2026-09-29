-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_translation_zero_and_translation_add
-- name    : AlgebraicGeometry.RiemannForm.translation_zero_and_translation_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/6e9747db-b042-5b43-8388-903819e12d82
-- title:
--   Translations of a relative group law: T₀=1_A and T_{P+Q}=T_P T_Q
-- statement:
--   Let $k$ be a field, let $A$ be a scheme (in universe $0$) and let $f : A \to \operatorname{Spec} k$ be a morphism. Let $L$ be a `RelativeGroupLaw` for $f$: for every scheme $T$ and every $t : T \to \operatorname{Spec} k$ a multiplication, a unit and an inversion on the set `SchemeHomOver t f` of morphisms $T \to A$ whose composition with $f$ is $t$, subject to associativity, two-sided unit law, left inverses, and naturality of the multiplication under base change along any $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Let `hc` assert that this multiplication is commutative for every $T$ and $t$, and let $P, Q$ be elements of `L.AlgPoints hc k`, the additive copy of the group of $k$-points, i.e. of the sections of $f$ over $\operatorname{Spec}$ of the identity map $k \to k$, with addition given by $L$. For a point $x$ of `Pt f`, `translation f L x` denotes the underlying morphism $A \to A$ of the $A$-valued point obtained by multiplying, under $L$ over $t = f$, the identity point $\mathbf{1}_A$ by the constant point $f$ followed by $x$. The assertion is the conjunction: the translation by the zero element of `L.AlgPoints hc k` is $\mathbf 1_A$, and the translation by $P+Q$ equals the translation by $P$ followed by the translation by $Q$.
--
--   This is the statement that $x \mapsto T_x$ is a group homomorphism from the $k$-points of $A$ into the endomorphisms of $A$ under composition, the elementary functor-of-points fact underlying the use of translations in the construction of Riemann forms and level pairings. It is used in the constructions of pullbacks of line bundles along translations by torsion points, of the associated cocycle for a rigidified bundle, and in the proof that level-pairing values are roots of unity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_translation_zero_and_translation_add.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.translation_zero_and_translation_add
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (P Q : L.AlgPoints hc k) :
    translation f L (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)) = 𝟙 A ∧
    translation f L (RelativeGroupLaw.AlgPoints.toPoint (P + Q)) =
      translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint Q) := by sorry
