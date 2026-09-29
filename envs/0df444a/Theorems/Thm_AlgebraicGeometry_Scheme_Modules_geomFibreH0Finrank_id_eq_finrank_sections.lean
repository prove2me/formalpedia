-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_id_eq_finrank_sections
-- name    : AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_id_eq_finrank_sections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/1974e30c-1d49-5e04-a7cc-0e969e7f347d
-- title:
--   Geometric fibre h⁰ along id_k equals dim_kΓ(A,M)
-- statement:
--   Let $k$ be a field, let $A$ be a scheme and let $f\colon A \to \operatorname{Spec} k$ be proper, and let $M$ be a module over the structure sheaf of $A$ which is invertible in the sense of the project's predicate `Scheme.Modules.IsInvertible`: every point of $A$ has an open neighbourhood $U$ containing it such that the pullback of $M$ along the inclusion $U \hookrightarrow A$ is isomorphic to the unit module on $U$. The assertion is an equality of natural numbers. On the left, `Scheme.Modules.geomFibreH0Finrank f M k (RingHom.id k)` is, by definition, the $k$-dimension of $\Gamma$ over the whole space of the pullback of $M$ along the first projection $\mathrm{pr}_1\colon A \times_{\operatorname{Spec} k} \operatorname{Spec} k \to A$, the $k$-structure being the one obtained by restriction of scalars along the ring map $k \cong \Gamma(\operatorname{Spec} k, \top) \to \Gamma(A \times_{\operatorname{Spec} k} \operatorname{Spec} k, \top)$ induced by the second projection. On the right stands the $k$-dimension of $\Gamma(M, \top)$, with the $k$-module structure given by restriction of scalars along the map $k \cong \Gamma(\operatorname{Spec} k, \top) \to \Gamma(A, \top)$ induced by $f$.
--
--   This identifies the "geometric fibre" invariant $h^0$ evaluated at the identity base change with the plain dimension of the space of global sections of an invertible module on a proper $k$-scheme, so that results phrased in terms of Čech $\check H^0$, Čech ranks and Euler characteristics can be fed into the polarisation and Hilbert-function arguments; it is used in the treatment of polarised abelian schemes and of the Hilbert functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_id_eq_finrank_sections.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_id_eq_finrank_sections
    (k : Type u) [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) :
    Scheme.Modules.geomFibreH0Finrank f M k (RingHom.id k) =
      (letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤; Module.finrank k Γ(M, ⊤)) := by sorry
