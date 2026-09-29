-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exteriorPower_map_app_unit_iotaMulti_eq_det_smul
-- name    : AlgebraicGeometry.Scheme.Modules.exteriorPower_map_app_unit_iotaMulti_eq_det_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/7e56cd75-43c2-5167-a965-f3d45c130b4d
-- title:
--   Exterior power of a morphism scales wedges by det a
-- statement:
--   Let $X$ be a scheme, $n$ a natural number, $M,N$ sheaves of $\mathcal{O}_X$-modules on $X$ (objects of `X.Modules`), $\varphi \colon M \to N$ a morphism of such sheaves, and $U$ an open subset of $X$. Let $e \colon \mathrm{Fin}\,n \to \Gamma(M,U)$ and $f \colon \mathrm{Fin}\,n \to \Gamma(N,U)$ be families of sections and $a$ an $n \times n$ matrix over $\Gamma(X,U)$ such that for every index $j$ one has $\varphi_U(e_j) = \sum_i a_{ij} \cdot f_i$ in $\Gamma(N,U)$. Write $\Lambda^{\mathrm{pre}}_n$ for the functor `Scheme.Modules.presheafExteriorPower X n`, which sends a presheaf of modules $P$ over the presheaf of rings of $X$ to the presheaf $V \mapsto \bigwedge^n_{\Gamma(X,V)} P(V)$, and recall that `Scheme.Modules.exteriorPower X n` is obtained by forgetting the sheaf condition, applying $\Lambda^{\mathrm{pre}}_n$, and sheafifying along the identity of the sheaf of rings of $X$, with $\det_n N$ its value at $N$. Let $\eta$ denote the unit of the sheafification adjunction for presheaves of modules. The assertion is the identity of sections over $U$
--   $$\big((\textstyle\bigwedge^n \varphi)_U\big)\big(\eta_{\Lambda^{\mathrm{pre}}_n M}(e_1 \wedge \dots \wedge e_n)\big) = \det(a)\cdot \eta_{\Lambda^{\mathrm{pre}}_n N}(f_1 \wedge \dots \wedge f_n)$$
--   in $\Gamma(\det_n N, U)$, where $e_1 \wedge \dots \wedge e_n$ and $f_1 \wedge \dots \wedge f_n$ are the images of $e$ and $f$ under the canonical alternating map into $\bigwedge^n$ over $\Gamma(X,U)$. No linear independence or freeness hypothesis is imposed on $e$ or $f$.
--
--   This is the sheaf-theoretic form of the classical fact that an $n \times n$ change-of-generators matrix acts on top exterior powers through its determinant. It is the computational core of the determinant/exterior-power machinery for sheaves of modules on a scheme, and is used in establishing the existence of local frames with prescribed norm behaviour and the criterion expressing the failure of a morphism to be an isomorphism through the vanishing of a determinant section.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exteriorPower_map_app_unit_iotaMulti_eq_det_smul.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesDet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.Modules.exteriorPower_map_app_unit_iotaMulti_eq_det_smul
    {X : Scheme.{u}} {n : ℕ} {M N : X.Modules} (φ : M ⟶ N) {U : X.Opens}
    (e : Fin n → Γ(M, U)) (f : Fin n → Γ(N, U)) (a : Matrix (Fin n) (Fin n) Γ(X, U))
    (ha : ∀ j, φ.app U (e j) = ∑ i, a i j • f i) :
    ((Scheme.Modules.exteriorPower X n).map φ).app U
        (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            ((Scheme.Modules.presheafExteriorPower X n).obj M.val)).app (op U)
          (show ((Scheme.Modules.presheafExteriorPower X n).obj M.val).obj (op U) from
            exteriorPower.ιMulti Γ(X, U) n e)) =
      a.det • (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            ((Scheme.Modules.presheafExteriorPower X n).obj N.val)).app (op U)
          (show ((Scheme.Modules.presheafExteriorPower X n).obj N.val).obj (op U) from
            exteriorPower.ιMulti Γ(X, U) n f) : Γ(Scheme.Modules.det n N, U)) := by sorry
