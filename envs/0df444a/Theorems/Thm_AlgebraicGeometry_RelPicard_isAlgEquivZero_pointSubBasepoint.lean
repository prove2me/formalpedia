-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_pointSubBasepoint
-- name    : AlgebraicGeometry.RelPicard.isAlgEquivZero_pointSubBasepoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/627c046d-9b1d-557d-a4c0-e1b28095af99
-- title:
--   𝒪(P-ε) is algebraically equivalent to zero
-- statement:
--   Let $k$ be a field and let $a \colon A \to \operatorname{Spec} k$ be a morphism of schemes that is separated, smooth of relative dimension $1$, geometrically integral and locally of finite type, and let $P$ and $\varepsilon$ be $k$-points of $A$, each given as a morphism $\operatorname{Spec} k \to A$ together with a proof that composing it with $a$ gives the identity of $\operatorname{Spec} k$. On the fibre product $A \times_{\operatorname{Spec} k, \,\mathrm{id}} \operatorname{Spec} k$ form the module $\mathcal{L} = \mathcal{I}_P^{-1} \otimes \mathcal{I}_\varepsilon$, where for a $k$-point $t$ the ideal sheaf $\mathcal{I}_t$ is the kernel ideal sheaf of the graph of $t$, carrying the structure of a relative effective Cartier divisor of degree $1$ (finite, flat, locally of finite presentation over the base with all fibre ranks equal to $1$), $\mathcal{I}_t^{-1}$ denoting its inverse module; pull $\mathcal{L}$ back along the canonical section $A \to A \times_{\operatorname{Spec} k} \operatorname{Spec} k$ obtained by lifting $\mathrm{id}_A$ and $a$. The assertion is that this module $L$ on $A$ satisfies `IsAlgEquivZero a`, that is: there exist a scheme $T'$ and a morphism $h \colon T' \to \operatorname{Spec} k$ that is locally of finite type and geometrically integral, a module $M$ on $A \times_{\operatorname{Spec} k} T'$ that is invertible (every point has an open neighbourhood on which $M$ restricts to a module isomorphic to the unit module), and two $k$-points $t_0, t_1$ of $T'$, such that the pullback of $M$ along the base change of $t_0$ is isomorphic to the unit module on $A \times_{\operatorname{Spec} k} \operatorname{Spec} k$, while the pullback of $M$ along the base change of $t_1$ is isomorphic to the pullback of $L$ along the first projection $A \times_{\operatorname{Spec} k} \operatorname{Spec} k \to A$.
--
--   This is the step "$P - \varepsilon$ is algebraically equivalent to zero" for a smooth geometrically integral curve over a field, in the form required by the project's cut-down notion of algebraic equivalence to zero for modules. It is used by [`AlgebraicGeometry.RelPicard.IsAlgEquivZero.of_iso_pointSubBasepoint`](thm.html#AlgebraicGeometry.RelPicard.IsAlgEquivZero.of_iso_pointSubBasepoint) and [`AlgebraicGeometry.RelPicard.IsAlgEquivZero.of_iso_pointsSubBasepoint`](thm.html#AlgebraicGeometry.RelPicard.IsAlgEquivZero.of_iso_pointsSubBasepoint), which transport the conclusion along isomorphisms of modules, and so feeds the identification of the degree-zero part of the relative Picard functor in the construction of the Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_pointSubBasepoint.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.isAlgEquivZero_pointSubBasepoint
    {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    [IsSeparated a] [SmoothOfRelativeDimension 1 a] [GeometricallyIntegral a] [LocallyOfFiniteType a]
    (P ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) :
    IsAlgEquivZero a ((Scheme.Modules.pullback (toProdSpec a)).obj (pointSubBasepointModule (a := a) P ε)) := by sorry
