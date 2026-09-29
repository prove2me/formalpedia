-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIso_stalkMap_pullback_fst_and_ringKrullDim_stalk_le_of_isFractionRing
-- name    : AlgebraicGeometry.isIso_stalkMap_pullback_fst_and_ringKrullDim_stalk_le_of_isFractionRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/7d3fc89f-06e5-5c86-b6d5-9014f1210040
-- title:
--   Stalks over the generic point equal stalks of the generic fibre
-- statement:
--   Let $R$ be a commutative integral domain and $K$ a field that is a fraction field of $R$ (an $R$-algebra with `IsFractionRing R K`), let $X$ be a scheme and $f \colon X \to \operatorname{Spec} R$ a morphism of schemes. Write $g = \operatorname{Spec}$ of the structure map $R \to K$ and form the fibre product $P = X \times_{\operatorname{Spec} R} \operatorname{Spec} K$ with first projection $\mathrm{pr} \colon P \to X$. The theorem asserts two things simultaneously. First, for every point $y$ of $P$ the induced map on stalks $\mathcal{O}_{X,\mathrm{pr}(y)} \to \mathcal{O}_{P,y}$ is an isomorphism of commutative rings. Second, for every natural number $n$: if $\operatorname{ringKrullDim} \mathcal{O}_{P,y} \le n$ for every point $y$ of $P$, then for every point $x$ of $X$ whose image $f(x)$ is the zero prime ideal of $R$ one has $\operatorname{ringKrullDim} \mathcal{O}_{X,x} \le n$. Here $\operatorname{ringKrullDim}$ takes values in $\mathbb{Z} \cup \{\pm\infty\}$ and the bound $\le n$ is the comparison with the image of the natural number $n$.
--
--   This is the standard identification of the local rings of $X$ at points lying over the generic point of $\operatorname{Spec} R$ with the local rings of the generic fibre $X_K$, together with the resulting bound on Krull dimensions of such stalks. It is used in the construction and analysis of integral models of modular curves, where a dimension bound on the characteristic-zero fibre is transported to the model, e.g. by [`ModularCurve.DRModelPackageLevel.flat_pi`](thm.html#ModularCurve.DRModelPackageLevel.flat_pi) and [`ModularCurve.IgusaScheme.free_localizedModule_sections_of_isRegularLocalRing_stalk_of_isFinite`](thm.html#ModularCurve.IgusaScheme.free_localizedModule_sections_of_isRegularLocalRing_stalk_of_isFinite).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIso_stalkMap_pullback_fst_and_ringKrullDim_stalk_le_of_isFractionRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isIso_stalkMap_pullback_fst_and_ringKrullDim_stalk_le_of_isFractionRing
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :
    (∀ y : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
        IsIso ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).stalkMap y)) ∧
    ∀ (n : ℕ),
      (∀ y : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
          ringKrullDim ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).presheaf.stalk y) ≤ n) →
      ∀ x : X, (f.base x).asIdeal = ⊥ → ringKrullDim (X.presheaf.stalk x) ≤ n := by sorry
