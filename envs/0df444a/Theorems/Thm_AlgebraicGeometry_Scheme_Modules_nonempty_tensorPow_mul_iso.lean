-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_tensorPow_mul_iso
-- name    : AlgebraicGeometry.Scheme.Modules.nonempty_tensorPow_mul_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/f5c7e272-bfbd-5840-9fc6-6279225d0853
-- title:
--   Tensor powers multiply: L^{⊗ ab}≅(L^{⊗ a})^{⊗ b}
-- statement:
--   Let $X$ be a scheme (in a fixed universe) and let $L$ be an object of $X.\mathrm{Modules}$, the monoidal category of sheaves of $\mathcal O_X$-modules on $X$. Tensor powers are defined by recursion: $L.\mathrm{tensorPow}\,0$ is the monoidal unit $\mathbb 1_{X.\mathrm{Modules}}$, and $L.\mathrm{tensorPow}\,(n+1)$ is $(L.\mathrm{tensorPow}\,n)\otimes L$, so the new factor is always appended on the right. The theorem asserts that for all natural numbers $a$ and $b$ the type of isomorphisms in $X.\mathrm{Modules}$ from $L.\mathrm{tensorPow}\,(a\cdot b)$ to $(L.\mathrm{tensorPow}\,a).\mathrm{tensorPow}\,b$ is nonempty; that is, there exists an isomorphism of sheaves of $\mathcal O_X$-modules $L^{\otimes ab}\cong(L^{\otimes a})^{\otimes b}$. Only the existence of such an isomorphism is claimed: no particular choice is exposed, and no compatibility or naturality in $a$, $b$ or $L$ is asserted. There are no hypotheses on $X$ or $L$ beyond the ambient typeclass structure of schemes and of the monoidal category of modules.
--
--   This is the elementary multiplicativity of tensor powers of a sheaf of modules, recorded in the form needed to replace a family of tensor powers by a single common power. It is used by [`AlgebraicGeometry.Scheme.Modules.exists_finiteBySections_tensorPow_of_forall_geometricFibre`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_finiteBySections_tensorPow_of_forall_geometricFibre) and by [`AlgebraicGeometry.RelPicard.exists_finiteBySections_tensorPow_thetaBundle_of_isAlgClosed`](thm.html#AlgebraicGeometry.RelPicard.exists_finiteBySections_tensorPow_thetaBundle_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_nonempty_tensorPow_mul_iso.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry MonoidalCategory

theorem AlgebraicGeometry.Scheme.Modules.nonempty_tensorPow_mul_iso {X : Scheme.{u}} (L : X.Modules) (a b : ℕ) :
    Nonempty (L.tensorPow (a * b) ≅ (L.tensorPow a).tensorPow b) := by sorry
