-- Prove2me | Theorems.Thm_BundleGerbeStable_exp_boundary_equiv
-- name    : BundleGerbeStable.exp_boundary_equiv
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:49:22.090284+00:00
-- url     : https://prove2.me/theorems/567efe39-5b35-4ed4-bf43-11747fc79a59
-- title:
--   The isomorphism $H^2(M,\mathbb C^\times)\simeq H^3(M,\mathbb Z)$
-- statement:
--   Let $M$ be a smooth manifold. There is an isomorphism of abelian groups
--   $$e:H^2(M,\mathbb C^\times)\xrightarrow{\ \simeq\ }H^3(M,\mathbb Z)$$
--   such that $e(a)=c$ exactly when $a$ and $c$ are related through the exponential sequence: on some cover, $a$ is the class of a cocycle $g=\exp(2\pi i f)$ with $f$ a smooth $\mathbb C$-valued cochain, and $c$ is the class of the integer-valued cocycle $\delta f$.
--
--   This identification lets the Dixmier-Douady class take values in $H^3(M,\mathbb Z)$.
--
--   Differences from the source:
--   - reading: "a manifold M" → M a finite-dimensional boundaryless smooth manifold of constant model E, Hausdorff and paracompact, with its manifold diffeology; no second countability, compactness or connectedness; reason: the paper's d(P) uses open covers with contractible intersections and H²(M, ℂ×) ≃ H³(M, ℤ) uses smooth partitions of unity; infinite-dimensional spaces occur in the paper as Y, not as this M
--   - encoding: H³(M, ℤ), H²(M, ℂ×) (the paper computes with Čech cocycles) → the colimit over covers of Čech cohomology on all tuples, of the presheaves of locally constant ℤ-valued and smooth ℂˣ-valued functions, presented by a direct sum of cocycles modulo coboundaries and refinement; reason: Mathlib's Sheaf.H has no map from Čech cocycles; for paracompact Hausdorff M this colimit is sheaf cohomology
--   - encoding: H²(M, ℂ×) ≃ H³(M, ℤ), with no sign fixed → n = +δf where exp(2πi f) = g (IsExpBoundary); reason: the paper fixes none; the choice changes no statement of the mission
-- source:
--   Murray, Stevenson, Bundle gerbes: stable isomorphism and local theory, arXiv:math/9908135v1, https://arxiv.org/abs/math/9908135v1, §2, p.3

import Mathlib
import Definitions.Def_BundleGerbeStable_IsDixmierDouady

open Manifold ContDiff

namespace BundleGerbeStable

universe u

/-- **The isomorphism `H²(M, ℂ×) ≃ H³(M, ℤ)`** (Murray, Stevenson, *Bundle gerbes: stable isomorphism and local theory*, arXiv:math/9908135v1, §2, p.3), of abelian groups, given by the
exponential sequence: `e a = c` exactly when `IsExpBoundary a c`. -/
theorem exp_boundary_equiv (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [ParacompactSpace M] [DiffeologicalSpace M] [IsManifoldDiffeology E M] :
    ∃ e : H2Cx M ≃+ H3 M, ∀ (a : H2Cx M) (c : H3 M), IsExpBoundary a c ↔ e a = c := by sorry

end BundleGerbeStable
