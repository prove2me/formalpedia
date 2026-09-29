-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso_pullback_of_isIso
-- name    : AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso_pullback_of_isIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/41adb7a3-af02-5a39-b0db-3ff03f80cb63
-- title:
--   Transport of Čech cohomology of an invertible sheaf along a scheme isomorphism
-- statement:
--   Let $R$ be a commutative ring, let $P$ and $P'$ be schemes, let $\pi' : P' \to \operatorname{Spec} R$ be separated, and let $\Phi : P \to P'$ be an isomorphism, so that $P$ becomes an $R$-scheme via $\Phi$ followed by $\pi'$. Let $N'$ be a module on $P'$ which is invertible in the sense of `Scheme.Modules.IsInvertible`, i.e. every point of $P'$ lies in an open $U$ for which the pullback of $N'$ along the inclusion $U \hookrightarrow P'$ admits an isomorphism to the unit sheaf of modules on $U$; let $N$ be a module on $P$ together with an isomorphism $e : N \cong \Phi^{*}N'$. Finally let $\mathfrak W$ and $\mathfrak W'$ be ordered affine covers of $P$ and of $P'$ respectively, each given by a finite linearly ordered index type and a family of affine opens whose supremum is the whole scheme. Both Čech complexes are formed from the sections data `OModulePresheaf.ofModules`, namely $U \mapsto \Gamma(N,U)$ with its $R$-module structure coming from the structure morphism, and $H^0$ denotes the kernel of the zeroth differential while `HSucc` at index $j$ denotes $\ker d_{j+1} / \operatorname{im} d_j$. The conclusion asserts that there exists an $R$-linear isomorphism between the $H^0$ of $N$ computed with $\mathfrak W$ and the $H^0$ of $N'$ computed with $\mathfrak W'$, and that for every $j \in \mathbb N$ there exists an $R$-linear isomorphism between the corresponding `HSucc` modules at index $j$. The isomorphisms are asserted only as nonemptiness statements, with no compatibility or naturality claimed.
--
--   This is the module-level transport statement for alternating Čech cohomology of an invertible sheaf: it identifies the cohomology of two presentations of the same geometric situation, with the covers on the two sides completely unrelated, using separatedness of the base morphism together with local triviality of the sheaf. It is used wherever Čech cohomology modules (and hence their lengths or torsion, not merely their vanishing) must be moved between a scheme and an isomorphic copy of it, for instance between a fibre of a family presented as a pullback and its affine slice presentation in the relative Picard and polarisation material.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso_pullback_of_isIso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso_pullback_of_isIso
    {R : Type u} [CommRing R] {P P' : Scheme.{u}} (π' : P' ⟶ Spec (CommRingCat.of R)) [IsSeparated π']
    (Φ : P ⟶ P') [IsIso Φ]
    (N' : P'.Modules) (hN' : Scheme.Modules.IsInvertible N')
    (N : P.Modules) (e : N ≅ (Scheme.Modules.pullback Φ).obj N')
    (𝔚 : P.OrderedAffineCover) (𝔚' : P'.OrderedAffineCover) :
    Nonempty ((OModulePresheaf.ofModules (Φ ≫ π') N).H0 𝔚 ≃ₗ[R] (OModulePresheaf.ofModules π' N').H0 𝔚') ∧
      ∀ j : ℕ, Nonempty ((OModulePresheaf.ofModules (Φ ≫ π') N).HSucc 𝔚 j ≃ₗ[R]
        (OModulePresheaf.ofModules π' N').HSucc 𝔚' j) := by sorry
