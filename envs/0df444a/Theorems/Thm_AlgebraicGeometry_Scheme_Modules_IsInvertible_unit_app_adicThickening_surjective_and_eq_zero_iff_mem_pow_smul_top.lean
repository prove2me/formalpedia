-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_unit_app_adicThickening_surjective_and_eq_zero_iff_mem_pow_smul_top
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.unit_app_adicThickening_surjective_and_eq_zero_iff_mem_pow_smul_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/76cf3c29-b304-5aca-9658-5383edc60eba
-- title:
--   Unit of the adic thickening adjunction: surjectivity and kernel Iⁿ⁺¹Γ(U,N)
-- statement:
--   Let $R$ be a commutative ring, $I\subseteq R$ an ideal, $X$ a scheme and $f\colon X\to\operatorname{Spec} R$ a morphism. Let $N$ be a sheaf of modules on $X$ satisfying `Scheme.Modules.IsInvertible`, i.e. every point of $X$ has an open neighbourhood $U$ such that the pullback of $N$ along the inclusion $U\hookrightarrow X$ is isomorphic to the unit module (the structure sheaf) of $U$. Let $n\in\mathbb N$ and let $U$ be an affine open of $X$. Write $\iota_n=$ `adicThickeningι f I n` for the morphism to $X$ from `adicThickening f I n`, the fibre product of $f$ with $\operatorname{Spec}(R/I^{n+1})\to\operatorname{Spec} R$, and consider the component at $U$ of the unit $N\to (\iota_n)_*\iota_n^{*}N$ of the pullback–pushforward adjunction along $\iota_n$. The assertion is twofold: this map on sections over $U$ is surjective; and, for a section $s\in\Gamma(N,U)$, it sends $s$ to $0$ if and only if $s$ lies in $I^{n+1}\cdot\top$, the submodule $I^{n+1}\Gamma(N,U)$ for the $R$-module structure on $\Gamma(N,U)$ given by `OModulePresheaf.ofModules f N`, in which $R$ acts through the ring map $R\to\Gamma(X,U)$ induced by $f$.
--
--   This is the affine-local form of the statement that sections of an invertible module restrict surjectively to the $n$-th adic thickening $X\times_{\operatorname{Spec} R}\operatorname{Spec}(R/I^{n+1})$, with kernel exactly $I^{n+1}$ times the sections. It is used in the construction of an isomorphism of invertible modules from a compatible family of isomorphisms over the adic thickenings ([`AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_compatible_pullback_adicThickening_iso`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_compatible_pullback_adicThickening_iso)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_unit_app_adicThickening_surjective_and_eq_zero_iff_mem_pow_smul_top.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_AdicThickening

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.unit_app_adicThickening_surjective_and_eq_zero_iff_mem_pow_smul_top
    {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    (N : X.Modules) (hN : Scheme.Modules.IsInvertible N) (n : ℕ) (U : X.affineOpens) :
    Function.Surjective
        (((Scheme.Modules.pullbackPushforwardAdjunction (adicThickeningι f I n)).unit.app N).app U.1) ∧
      ∀ s : (OModulePresheaf.ofModules f N).obj U.1,
        ((Scheme.Modules.pullbackPushforwardAdjunction (adicThickeningι f I n)).unit.app N).app U.1 s = 0 ↔
          s ∈ I ^ (n + 1) • (⊤ : Submodule R ((OModulePresheaf.ofModules f N).obj U.1)) := by sorry
