-- Prove2me | Theorems.Thm_AlgebraicGeometry_isSeparated_sigmaDesc_of_forall_isSeparated
-- name    : AlgebraicGeometry.isSeparated_sigmaDesc_of_forall_isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/714b510e-f301-5782-a188-51ff8fc2011a
-- title:
--   Separatedness of a coproduct of separated morphisms
-- statement:
--   Let $\sigma$ be a type, let $X : \sigma \to \mathrm{Scheme}$ be a family of schemes indexed by $\sigma$, let $Y$ be a scheme, and let $f_i : X_i \to Y$ be a morphism of schemes for each $i \in \sigma$. Assume that every $f_i$ is separated, that is, for each $i$ the diagonal morphism $X_i \to X_i \times_Y X_i$ is a closed immersion. The conclusion is that the morphism $\coprod_{i \in \sigma} X_i \to Y$ induced by the family $(f_i)_i$ out of the coproduct of the $X_i$ in the category of schemes, namely `Sigma.desc f`, is again separated: its diagonal $\coprod_i X_i \to (\coprod_i X_i) \times_Y (\coprod_i X_i)$ is a closed immersion. All schemes and the index type live in a single universe $u$.
--
--   This is the standard fact that separatedness of morphisms to a fixed base is stable under taking disjoint unions of the sources. It serves as scheme-theoretic infrastructure for constructions in which a morphism is assembled from a family of morphisms over a common base, such as a structure morphism of a disjoint union of pieces indexed by Hilbert polynomials; it is used in the assembly of such a stratified family into a single separated morphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isSeparated_sigmaDesc_of_forall_isSeparated.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isSeparated_sigmaDesc_of_forall_isSeparated
    {σ : Type u} (X : σ → Scheme.{u}) {Y : Scheme.{u}} (f : ∀ i, X i ⟶ Y)
    (hf : ∀ i, IsSeparated (f i)) : IsSeparated (Sigma.desc f) := by sorry
