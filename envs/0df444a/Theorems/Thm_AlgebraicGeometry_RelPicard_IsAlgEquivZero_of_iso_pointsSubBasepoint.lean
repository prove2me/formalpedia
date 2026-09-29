-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_of_iso_pointsSubBasepoint
-- name    : AlgebraicGeometry.RelPicard.IsAlgEquivZero.of_iso_pointsSubBasepoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/c965f6f7-c5c4-5cd7-a0ad-9e049c1894cd
-- title:
--   Abel–Jacobi: 𝒪(sum Pᵢ - rε) is algebraically equivalent to zero
-- statement:
--   Let $k$ be a field and let $a \colon A \to \operatorname{Spec} k$ be a separated morphism which is smooth of relative dimension $1$, geometrically integral and locally of finite type. Let $\varepsilon$ be a section of $a$ over the identity of $\operatorname{Spec} k$, that is a morphism $\operatorname{Spec} k \to A$ composing with $a$ to the identity, and let $Ps$ be a list of such sections. Let $L$ be a module over the structure sheaf of $A$, and suppose given an isomorphism $e$ between the pullback of $L$ along $\mathrm{pr}_1 \colon A \times_{\operatorname{Spec} k} \operatorname{Spec} k \to A$ and `pointsSubBasepointModule` of $\varepsilon$ and $Ps$, the tensor product, taken over the list with the monoidal unit for the empty list, of the factors $\mathcal{O}(P) \otimes \mathcal{I}_\varepsilon$, where $\mathcal{O}(P)$ is the line bundle of the relative effective Cartier divisor cut out by $P$ and $\mathcal{I}_\varepsilon$ the ideal module of the one cut out by $\varepsilon$. The conclusion is `IsAlgEquivZero a L`: there exist a scheme $T'$, a locally of finite type, geometrically integral morphism $h \colon T' \to \operatorname{Spec} k$, a locally trivial module $M$ on $A \times_{\operatorname{Spec} k} T'$, and two sections $t_0, t_1$ of $h$, such that the pullback of $M$ along the base change of $t_0$ is isomorphic to the structure sheaf of $A \times_{\operatorname{Spec} k} \operatorname{Spec} k$, while its pullback along the base change of $t_1$ is isomorphic to $\mathrm{pr}_1^{*} L$.
--
--   This is the Abel–Jacobi statement that a divisor class of the form $\sum_i P_i - r\varepsilon$, with all $P_i$ and the basepoint $\varepsilon$ rational sections of a smooth geometrically integral relative curve, lies in the $\mathrm{Pic}^0$ cut, realised here as algebraic equivalence to zero by an explicit connecting family. It is used in the treatment of the Jacobian and its Néron model, for the computation of the cut by Euler characteristics and in the Deligne–Rapoport model package for modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_of_iso_pointsSubBasepoint.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.IsAlgEquivZero.of_iso_pointsSubBasepoint
    {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    [IsSeparated a] [SmoothOfRelativeDimension 1 a] [GeometricallyIntegral a] [LocallyOfFiniteType a]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) (Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a))
    {L : A.Modules}
    (e : (Scheme.Modules.pullback (pullback.fst a (𝟙 _))).obj L ≅ pointsSubBasepointModule (a := a) ε Ps) :
    IsAlgEquivZero a L := by sorry
