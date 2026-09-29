-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_iff_isLocalizedModule
-- name    : AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_iff_isLocalizedModule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/e8e37f1c-46ab-5e70-8950-b9bf0d2cbc6b
-- title:
--   Recognising ̃Γ(M)toM on basic opens
-- statement:
--   Let $R$ be a commutative ring (an object of `CommRingCat` in universe $u$) and let $M$ be a sheaf of modules on the affine scheme $\operatorname{Spec} R$, i.e. an object of `(Spec (.of R)).Modules`. The assertion is an equivalence between two statements. The first is that the canonical comparison morphism `M.fromTildeΓ`, from the sheaf of modules associated with the $R$-module of global sections of $M$ to $M$ itself, is an isomorphism. The second is that for every element $f : R$ the following holds: pass to the sheaf of $R$-modules on the underlying topological space of $\operatorname{Spec} R$ via `modulesSpecToSheaf`, take its restriction map along the inclusion $D(f) =$ `PrimeSpectrum.basicOpen f` $\le \top$, and regard the resulting morphism as an $R$-linear map between the module of global sections and the module of sections over $D(f)$; this linear map is required to satisfy `IsLocalizedModule (Submonoid.powers f)`, that is, to exhibit the sections over $D(f)$ as the localisation of the global sections at the multiplicative submonoid of powers of $f$ (the submonoid being taken inside $R$).
--
--   This is the recognition principle for sheaves of modules on an affine scheme coming from a module: the comparison map from the sheaf associated with the global sections is an isomorphism exactly when sections over each basic open are the expected localisation. It is used in the project to verify this condition in concrete situations, via [`AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_of_isLocalization_basicOpen`](thm.html#AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_of_isLocalization_basicOpen) and [`AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_pushforward_of_locallyTrivial`](thm.html#AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_pushforward_of_locallyTrivial).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_iff_isLocalizedModule.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_iff_isLocalizedModule {R : CommRingCat.{u}}
    (M : (Spec (.of R)).Modules) :
    IsIso M.fromTildeΓ ↔ ∀ f : R, IsLocalizedModule (Submonoid.powers (M := R) f)
      ((modulesSpecToSheaf.obj M).1.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom := by sorry
