-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_mul_mul_tensor_iso
-- name    : AlgebraicGeometry.Scheme.Modules.nonempty_pullback_mul_mul_tensor_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/d501415b-cc0c-5ba2-8aa2-04044e623083
-- title:
--   Theorem of the cube in pullback form
-- statement:
--   Let $k$ be an algebraically closed field, let $X$ be a scheme over $k$ via $t \colon X \to \operatorname{Spec} k$, and suppose the object $X$ of the category of schemes over $\operatorname{Spec} k$ carries the structure of a group object whose multiplication is commutative; assume $t$ is smooth, proper and geometrically connected. Let $L$ be a module over $X$ which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ with the pullback of $L$ along the inclusion $U \hookrightarrow X$ isomorphic to the unit module of $U$. Let $Y$ be any scheme over $\operatorname{Spec} k$ and let $f, g, h \colon Y \to X$ be three morphisms over $\operatorname{Spec} k$, multiplied in the group $X(Y)$ induced by the group-object structure. The conclusion is that the set of isomorphisms of modules over the underlying scheme of $Y$
--   $$(fgh)^*L \otimes f^*L \otimes g^*L \otimes h^*L \;\cong\; (fg)^*L \otimes (fh)^*L \otimes (gh)^*L$$
--   is nonempty, all pullbacks being taken along the underlying morphisms of schemes and the tensor products being right-associated.
--
--   This is the theorem of the cube for an abelian variety over an algebraically closed field, in its pullback (three-parameter) form, stated multiplicatively so that no inverse line bundles occur. It is used to derive the translation formula for pullbacks of an invertible module, the comparison of $[n]^*L$ with tensor powers of $L$ for symmetric $L$, and, through those, the degree identities for endomorphisms needed in the study of Jacobians with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_mul_mul_tensor_iso.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

open scoped CategoryTheory.MonObj

theorem AlgebraicGeometry.Scheme.Modules.nonempty_pullback_mul_mul_tensor_iso
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [GrpObj (Over.mk t)] [IsCommMonObj (Over.mk t)]
    (hsm : Smooth t) (hpr : IsProper t) (hgc : GeometricallyConnected t)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    {Y : Over (Spec (CommRingCat.of k))} (f g h : Y ⟶ Over.mk t) :
    Nonempty (
      (Scheme.Modules.pullback (f * g * h).left).obj L ⊗ (Scheme.Modules.pullback f.left).obj L ⊗
          (Scheme.Modules.pullback g.left).obj L ⊗ (Scheme.Modules.pullback h.left).obj L ≅
        (Scheme.Modules.pullback (f * g).left).obj L ⊗ (Scheme.Modules.pullback (f * h).left).obj L ⊗
          (Scheme.Modules.pullback (g * h).left).obj L) := by sorry
