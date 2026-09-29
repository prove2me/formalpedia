-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_baseChange_sections_linearEquiv_pushforward_tensorUnit_of_affineOpen_le
-- name    : AlgebraicGeometry.Scheme.Modules.exists_baseChange_sections_linearEquiv_pushforward_tensorUnit_of_affineOpen_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/1a93e7e0-0e40-53f9-b5ad-53a2597322af
-- title:
--   Restriction of π_*mathcal O_Y between affine opens is a base change
-- statement:
--   Let $X$ and $Y$ be schemes (in a fixed universe) and let $\pi : Y \to X$ be a morphism that is an affine morphism, i.e. carries the `IsAffineHom` property. Let $U$ and $V$ be open subsets of $X$, both affine open, with $V \le U$, and equip $\Gamma(X, V)$ with the $\Gamma(X, U)$-algebra structure coming from the restriction ring map $\Gamma(X, U) \to \Gamma(X, V)$ of the structure presheaf of $X$. Write $\pi_*\mathcal O_Y$ for the sheaf of $\mathcal O_X$-modules obtained by applying the pushforward functor `Scheme.Modules.pushforward π` to the monoidal unit $\mathbb 1$ of the monoidal category of $\mathcal O_Y$-modules; its sections over an open $W \subseteq X$ form a $\Gamma(X, W)$-module. The assertion is that there exists a $\Gamma(X, V)$-linear isomorphism
--   $$e : \Gamma(X, V) \otimes_{\Gamma(X, U)} \Gamma(\pi_*\mathcal O_Y, U) \;\xrightarrow{\ \sim\ }\; \Gamma(\pi_*\mathcal O_Y, V)$$
--   which is normalised by $e(1 \otimes m) = m|_V$ for every section $m \in \Gamma(\pi_*\mathcal O_Y, U)$, where $m|_V$ denotes the image of $m$ under the restriction map of the presheaf $\pi_*\mathcal O_Y$ along $V \le U$.
--
--   This records the quasi-coherence of $\pi_*\mathcal O_Y$ for an affine morphism $\pi$ in the concrete form needed later: passing from an affine open $U$ to a smaller affine open $V$ is base change of the $\Gamma(X,U)$-module $\Gamma(\pi^{-1}U, \mathcal O_Y)$ along $\Gamma(X,U) \to \Gamma(X,V)$, with restriction of sections as the structural map. It is used in [`AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_basicOpen_refinement_basis_pushforward`](thm.html#AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_basicOpen_refinement_basis_pushforward), where bases of such modules of sections must be transported to a refinement of an affine open cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_baseChange_sections_linearEquiv_pushforward_tensorUnit_of_affineOpen_le.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.exists_baseChange_sections_linearEquiv_pushforward_tensorUnit_of_affineOpen_le
    {X Y : Scheme.{u}} (π : Y ⟶ X) [IsAffineHom π]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ U) :
    letI : Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
    ∃ e : Γ(X, V) ⊗[Γ(X, U)] Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), U) ≃ₗ[Γ(X, V)]
        Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), V),
      ∀ m : Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), U),
        e ((1 : Γ(X, V)) ⊗ₜ[Γ(X, U)] m) =
          ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE hVU).op m := by sorry
