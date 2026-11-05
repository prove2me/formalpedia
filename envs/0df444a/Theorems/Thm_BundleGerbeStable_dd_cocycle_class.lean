-- Prove2me | Theorems.Thm_BundleGerbeStable_dd_cocycle_class
-- name    : BundleGerbeStable.dd_cocycle_class
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:49:47.733845+00:00
-- url     : https://prove2.me/theorems/7208617e-4bc4-40a6-a2c4-24bee7e6b825
-- title:
--   $g_{\alpha\beta\gamma}$ defines exactly one class in $H^2(M,\mathbb C^\times)$
-- statement:
--   Let $(P,Y)$ be a bundle gerbe over a smooth manifold $M$. There is exactly one $a\in H^2(M,\mathbb C^\times)$ with the following property: for some open cover $\{U_\alpha\}$, smooth sections $s_\alpha:U_\alpha\to Y$ and smooth $\sigma_{\alpha\beta}:U_\alpha\cap U_\beta\to P$ over $(s_\alpha,s_\beta)$, the map $g_{\alpha\beta\gamma}$ defined by
--   $$\sigma_{\alpha\beta}\sigma_{\beta\gamma}=\sigma_{\alpha\gamma}g_{\alpha\beta\gamma}$$
--   is a smooth $\mathbb C^\times$-valued cocycle whose class is $a$.
--
--   Existence says that such data exist and that $g$ is a cocycle. Uniqueness says the class does not depend on the choices. Together with `exp_boundary_equiv` this makes the Dixmier-Douady class a function of $P$.
--
--   Differences from the source:
--   - generalization: Y and P in a category of spaces "deduced from context": finite-dimensional manifolds, infinite-dimensional manifolds, differentiable spaces (p.2) → Y and P diffeological spaces in the universe of M, π smooth and locally split, with local triviality by diffeomorphisms; reason: the paper leaves the category open; diffeological spaces contain each named category, and a smooth map between manifolds is a diffeologically smooth one
--   - reading: "a manifold M" → M a finite-dimensional boundaryless smooth manifold of constant model E, Hausdorff and paracompact, with its manifold diffeology; no second countability, compactness or connectedness; reason: the paper's d(P) uses open covers with contractible intersections and H²(M, ℂ×) ≃ H³(M, ℤ) uses smooth partitions of unity; infinite-dimensional spaces occur in the paper as Y, not as this M
--   - encoding: H³(M, ℤ), H²(M, ℂ×) (the paper computes with Čech cocycles) → the colimit over covers of Čech cohomology on all tuples, of the presheaves of locally constant ℤ-valued and smooth ℂˣ-valued functions, presented by a direct sum of cocycles modulo coboundaries and refinement; reason: Mathlib's Sheaf.H has no map from Čech cocycles; for paracompact Hausdorff M this colimit is sheaf cohomology
--   - encoding: an open cover with all intersections contractible → any open cover, as a set of open sets, carrying sections s_α and maps σ_αβ; reason: contractibility is used on p.3 only to make the σ_αβ exist, a cover of the paper's kind is one such cover, and the class does not depend on the choice (dd_cocycle_class)
-- source:
--   Murray, Stevenson, Bundle gerbes: stable isomorphism and local theory, arXiv:math/9908135v1, https://arxiv.org/abs/math/9908135v1, §2, p.3

import Mathlib
import Definitions.Def_BundleGerbeStable_IsDixmierDouady

open Manifold ContDiff

namespace BundleGerbeStable

universe u

/-- **The class in `H²(M, ℂ×)`** (Murray, Stevenson, *Bundle gerbes: stable isomorphism and local theory*, arXiv:math/9908135v1, §2, p.3): the map `g_αβγ` defined by
`σ_αβ σ_βγ = σ_αγ g_αβγ` "is a ℂ× valued cocycle and defines the Dixmier-Douady class in H²(M, ℂ×)".
Every bundle gerbe has such a cocycle (existence, which includes the cocycle identity for `g`), and
its class does not depend on the cover, the sections `s_α` or the maps `σ_αβ` (uniqueness). -/
theorem dd_cocycle_class (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [ParacompactSpace M] [DiffeologicalSpace M] [IsManifoldDiffeology E M]
    {S : LocallySplit.{u} M} (P : BundleGerbe S) :
    ∃! a : H2Cx M, IsDDCocycle P a := by sorry

end BundleGerbeStable
