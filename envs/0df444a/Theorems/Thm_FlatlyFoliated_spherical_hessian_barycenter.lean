-- Prove2me | Theorems.Thm_FlatlyFoliated_spherical_hessian_barycenter
-- name    : FlatlyFoliated.spherical_hessian_barycenter
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T18:17:35.442108+00:00
-- url     : https://prove2.me/theorems/31c148d7-08a9-4231-9958-2dd15b0a776f
-- title:
--   Spherical averaging of second derivatives as a Hessian barycenter
-- statement:
--   For every smooth real function $f$ on $\mathbb R^3$, its spherical average $\bar f$ is smooth. At each point $x$, there is a probability distribution on pairs $(\ell,A)$, where $A$ is a real $3\times3$ tensor with the Frobenius norm, whose barycenter is
--   $$\left(\Delta\bar f(x),\operatorname{Hess}\bar f(x)\right).$$
--   Both coordinates are integrable. Almost every pair comes from the second-derivative invariants of $f$ on the sphere through $x$: for some $y$ with $|y|=|x|$,
--   $$\ell=\Delta f(y),\qquad \|A\|^2=\|\operatorname{Hess}f(y)\|^2.$$
--   Moreover, $(\Delta f(x),\operatorname{Hess}f(x))$ belongs to the topological support of the distribution.
--
--   This is the second-derivative barycenter formulation of rotational averaging in equations (75)–(78). It separates the calculus of spherical averaging from subsequent convexity arguments and has no field-equation, positivity, or decay assumption.
-- source:
--   Bray, Hamm, Hirsch, Wheeler, Zhang, Flatly Foliated Relativity, arXiv:1911.00967v2, https://arxiv.org/abs/1911.00967, Section 5, eqs. (75)–(78), rotational averaging and differentiation preceding Lemma 1.

import Definitions.Def_FlatlyFoliatedRelativity_basic

open scoped ContDiff Topology
open MeasureTheory

theorem FlatlyFoliated.spherical_hessian_barycenter
    (f : FlatlyFoliated.R3 → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (FlatlyFoliated.sphSymmetrization f) ∧
    ∀ x : FlatlyFoliated.R3,
      ∃ μ : Measure (ℝ × EuclideanSpace ℝ (Fin 3 × Fin 3)),
        IsProbabilityMeasure μ ∧
        Integrable (fun p => p.1) μ ∧ Integrable (fun p => p.2) μ ∧
        (∫ p, p.1 ∂μ) = FlatlyFoliated.lap (FlatlyFoliated.sphSymmetrization f) x ∧
        (∫ p, p.2 ∂μ) = WithLp.toLp 2
          (fun ij : Fin 3 × Fin 3 => FlatlyFoliated.pd ij.2
            (FlatlyFoliated.pd ij.1 (FlatlyFoliated.sphSymmetrization f)) x) ∧
        (∀ᵐ p ∂μ, ∃ y : FlatlyFoliated.R3, ‖y‖ = ‖x‖ ∧
          p.1 = FlatlyFoliated.lap f y ∧ ‖p.2‖ ^ 2 = FlatlyFoliated.hessNormSq f y) ∧
        (FlatlyFoliated.lap f x, WithLp.toLp 2
          (fun ij : Fin 3 × Fin 3 => FlatlyFoliated.pd ij.2 (FlatlyFoliated.pd ij.1 f) x))
            ∈ μ.support := by sorry
