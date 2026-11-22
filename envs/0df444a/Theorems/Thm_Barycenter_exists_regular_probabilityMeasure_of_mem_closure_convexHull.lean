-- Prove2me | Theorems.Thm_Barycenter_exists_regular_probabilityMeasure_of_mem_closure_convexHull
-- name    : Barycenter.exists_regular_probabilityMeasure_of_mem_closure_convexHull
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:09.60722+00:00
-- url     : https://prove2.me/theorems/7742f999-fe28-4719-adc6-29b300a3a02d
-- title:
--   Points of the closed convex hull of a compact set are barycentres of Radon probability measures on it
-- statement:
--   **Barycentres of compact sets (local representation of continuous linear forms).**
--
--   Let $E$ be a Hausdorff locally convex topological vector space over $\mathbb k=\mathbb R$ or $\mathbb C$, with continuous dual $E'$, and let $K\subseteq E$ be a compact subset. Let $x$ be a point of the closed convex hull $\overline{\mathrm{ch}}(K)$ of $K$ in $E$.
--
--   Then there exists a positive Radon measure $\mu$ on $K$ with $\mu(K)=1$ such that
--   $$\ell(x)=\int_K\ell(y)\,\mathrm d\mu(y)\qquad\text{for all }\ell\in E'.$$
--   In other words $x$ is the barycentre (the weak, i.e. Pettis, integral $\int_K y\,\mathrm d\mu(y)$) of a Radon probability measure carried by $K$.
--
--   The closed convex hull of $K$ need not be compact and $E$ need not be complete. In the paper this lemma supplies the measure in formula (49.1) of Trèves' description of the continuous dual of $E\otimes_\varepsilon F$ by integral bilinear forms (Proposition C.2.4.8), on which the characterisations of nuclearity rest.
--
--   **Formalization Note.** $\mu$ is a measure on the subtype `K` with the Borel $\sigma$-algebra induced from $E$ (`[MeasurableSpace E] [BorelSpace E]`); "Radon probability measure" is `IsProbabilityMeasure μ ∧ μ.Regular` on the compact Hausdorff space $K$. The real structure used for the convex hull is given by `[Module ℝ E] [IsScalarTower ℝ 𝕜 E]`, and local convexity is `LocallyConvexSpace ℝ E`. The scalar identity is the one stated in parentheses in the source (it is the definition of the Pettis integral there); integrability of $y\mapsto\ell(y)$, which is automatic, is asserted explicitly so that the Bochner integral is not a junk value. The source works over $\mathbb C$; the statement covers $\mathbb R$ and $\mathbb C$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 687–688, Lemma C.2.4.6 and (C.2.4.4); classical reference: outlined in F. Trèves, Topological Vector Spaces, Distributions and Kernels, pp. 500–501 (formula (49.1))

import Mathlib

open Topology MeasureTheory
set_option autoImplicit false

namespace Barycenter

theorem exists_regular_probabilityMeasure_of_mem_closure_convexHull {𝕜 E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [T2Space E]
    [MeasurableSpace E] [BorelSpace E] {K : Set E} (hK : IsCompact K) {x : E}
    (hx : x ∈ closure (convexHull ℝ K)) :
    ∃ μ : Measure K, IsProbabilityMeasure μ ∧ μ.Regular ∧
      ∀ ℓ : StrongDual 𝕜 E,
        Integrable (fun y : K => ℓ (y : E)) μ ∧ ∫ y : K, ℓ (y : E) ∂μ = ℓ x := by sorry

end Barycenter
