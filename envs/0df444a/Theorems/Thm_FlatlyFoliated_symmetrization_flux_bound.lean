-- Prove2me | Theorems.Thm_FlatlyFoliated_symmetrization_flux_bound
-- name    : FlatlyFoliated.symmetrization_flux_bound
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T18:05:33.745819+00:00
-- url     : https://prove2.me/theorems/6399d45d-6308-40fc-a75b-e156fa37b5dc
-- title:
--   Asymptotic upper bound for the vacuum symmetrization defect
-- statement:
--   Let $f$ be smooth on $\mathbb R^3$, approximately spherically symmetric at infinity, and satisfy
--   $$(\Delta f)^2-\|D^2f\|_F^2=2\Lambda.$$
--   Its spherical average $\bar f$ is smooth. Moreover, for every $\varepsilon>0$ there is $R_0>0$ such that, for every $R\ge R_0$,
--   $$\int_{B_R}\big((\Delta\bar f)^2-\|D^2\bar f\|_F^2-2\Lambda\big)\,dx\le\varepsilon.$$
--   Here approximate symmetry has the platform's definition: $f-\bar f$ is bounded and $r^2\|D^2(f-\bar f)\|\,\|D(f-\bar f)\|$ tends uniformly to zero outside large balls. This is the flux estimate before invoking nonnegativity of the integrand; no sign of $\Lambda$ or $\Delta f$ is required.
-- source:
--   Bray, Hamm, Hirsch, Wheeler, Zhang, Flatly Foliated Relativity, https://arxiv.org/html/1911.00967v2, Theorem 5 proof, equations (75)–(77) and (82)–(95). The operator-norm product in the platform approximate-symmetry definition bounds the quadratic boundary flux in (87).

import Definitions.Def_FlatlyFoliatedRelativity_basic

open scoped ContDiff
open MeasureTheory Metric FlatlyFoliated

theorem FlatlyFoliated.symmetrization_flux_bound (Λ : ℝ) (f : R3 → ℝ)
    (hf : ContDiff ℝ ∞ f) (happrox : FlatlyFoliated.ApproxSphSymmAtInfty f)
    (heq : ∀ x, FlatlyFoliated.lap f x ^ 2 - FlatlyFoliated.hessNormSq f x = 2 * Λ) :
    ContDiff ℝ ∞ (FlatlyFoliated.sphSymmetrization f) ∧
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ S : ℝ, R ≤ S →
      (∫ x in ball (0 : FlatlyFoliated.R3) S,
        (FlatlyFoliated.lap (FlatlyFoliated.sphSymmetrization f) x ^ 2 -
          FlatlyFoliated.hessNormSq (FlatlyFoliated.sphSymmetrization f) x - 2 * Λ)) ≤ ε := by sorry
