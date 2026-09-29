-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_of_forall_subsingleton_HSucc_baseChange_of_field
-- name    : AlgebraicGeometry.OModulePresheaf.subsingleton_HSucc_of_forall_subsingleton_HSucc_baseChange_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/65a1677e-1445-58ab-be99-e5ea1daf9f9c
-- title:
--   Vanishing of higher Čech cohomology descends along a field extension
-- statement:
--   Let $K$ be a field, let $X$ be a scheme and let $\pi : X \to \operatorname{Spec} K$ be a separated morphism. Let $\mathcal U$ be an ordered affine cover of $X$, that is, a finite linearly ordered index set together with affine open subsets $U_i \subseteq X$ whose supremum is $\top$, and let $M$ be a sheaf of $\mathcal O_X$-modules. Assume $M$ is locally trivial: every point $x \in X$ lies in an open $V$ such that the pullback of $M$ along the inclusion $V \hookrightarrow X$ is isomorphic to the unit module $\mathcal O_V$. Let $K'$ be a field equipped with a $K$-algebra structure. Form the pullback of $\pi$ along $\operatorname{Spec}$ of $K \to K'$, with projections $p_1$ to $X$ and $p_2$ to $\operatorname{Spec} K'$, and let $\mathcal U_{K'}$ be the cover obtained by taking preimages of the $U_i$ under $p_1$. Writing, for a morphism $c$ to an affine base and a sheaf of modules $N$, `ofModules` for the presheaf $U \mapsto \Gamma(N,U)$ with its module structures over the base ring and over $\Gamma(X,U)$ and its restriction maps, and writing $\mathrm{HSucc}$ at index $i$ for the quotient of $\ker d_{i+1}$ by the preimage of the range of $d_i$ in the associated complex, assume that $\mathrm{HSucc}$ of `ofModules` $p_2$ $(p_1^* M)$ with respect to $\mathcal U_{K'}$ is a subsingleton for every $i \in \mathbb N$. Then, for a given $i \in \mathbb N$, $\mathrm{HSucc}$ of `ofModules` $\pi$ $M$ with respect to $\mathcal U$ at $i$ is a subsingleton.
--
--   This is the descent half of flat base change for Čech cohomology in positive degrees: vanishing of the higher Čech cohomology of a locally trivial module after extension of the base field implies vanishing before extension. It is used as the final step in the fibrewise-vanishing arguments for modules on relative curves and on fake elliptic curves, where vanishing is first verified over an extension field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_of_forall_subsingleton_HSucc_baseChange_of_field.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.subsingleton_HSucc_of_forall_subsingleton_HSucc_baseChange_of_field
    {K : Type u} [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (.of K)) [IsSeparated π]
    (𝒰 : X.OrderedAffineCover) (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (K' : Type u) [Field K'] [Algebra K K']
    (h : ∀ i : ℕ, Subsingleton ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap K K'))
        ((Scheme.Modules.pullback (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap K K'))).obj M)).HSucc
        (𝒰.baseChange π K') i))
    (i : ℕ) :
    Subsingleton ((OModulePresheaf.ofModules π M).HSucc 𝒰 i) := by sorry
