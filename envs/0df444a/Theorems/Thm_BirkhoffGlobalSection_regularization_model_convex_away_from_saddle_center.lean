-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_regularization_model_convex_away_from_saddle_center
-- name    : BirkhoffGlobalSection.regularization_model_convex_away_from_saddle_center
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-28T03:12:18.609174+00:00
-- url     : https://prove2.me/theorems/d8584167-5e38-4f0c-bf68-b099fa7d5c8d
-- title:
--   Strict convexity away from the saddle-centers in a regularization model
-- statement:
--   Strict convexity away from the equal-mass saddle-centers persists near the critical energy, in a suitable regularization.
--
--   Let $U\subset\mathbb{R}^4$ be an open set containing the Levi-Civita points $S_\pm=(\pm\tfrac12,0,0,0)$, which lie over the first Lagrange point for $\mu=\tfrac12$ at the critical energy $c=2$. Then there exist $\varepsilon,\eta>0$ with the following property. Whenever
--
--   $$
--   0<\mu<1,\qquad |\mu-\tfrac12|<\varepsilon,\qquad c<2+\eta,\qquad -c<h_1(\mu),
--   $$
--
--   the selected Levi-Civita component $\Sigma_{\mu,c}$ admits a regularization model $(\Phi,G)$ such that
--
--   $$
--   \Phi(s)\ \text{is a strictly convex star-shaped point of } G\qquad\text{for every } s\in\Sigma_{\mu,c}\setminus U .
--   $$
--
--   A regularization model is a smooth symplectic (up to a positive constant) change of coordinates carrying the Levi-Civita flow to a model Hamiltonian flow up to a positive time change. A strictly convex star-shaped point is one where the model level set is radially transverse and has positive definite second fundamental form.
--
--   In Liu–Salomão, the equal-mass critical surface is strictly convex away from its two saddle-center singularities in the elliptic-hyperbolic regularization of Section 9.2 (Theorem 1.12, proved in Section 9). Section 10 uses this for nearby parameters on the part of the surface outside a neighborhood of the singularities. This statement makes that step explicit, with the centered elliptic-hyperbolic coordinates as the intended model. Convexity depends on the coordinates, so the statement is made in the model and not in Levi-Civita coordinates.
--
--   **Formalization Note** The model is `RegularizationModel μ c` and the pointwise condition is `IsStrictlyConvexStarShapedAt`, both from `Def_BirkhoffGlobalSection_RegularizationModel`. The model may depend on $U$ and on $(\mu,c)$.
-- source:
--   Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2. Theorem 1.12 (strict convexity at mu = 1/2 for E <= -2, proved in Section 9 via Theorems 9.1, 9.4 and Proposition 9.9); Section 9.2 (elliptic-hyperbolic regularization); Section 10, first paragraph (convexity of the critical surface used for nearby (mu, E) outside a neighborhood of the saddle-centers).

import Definitions.Def_BirkhoffGlobalSection_RegularizationModel

namespace BirkhoffGlobalSection

/-- Persistence of strict convexity away from the saddle-centers. Fix any open
set containing the Levi-Civita lifts `(±1/2, 0, 0, 0)` of the first Lagrange
point for `μ = 1/2`. For parameters in a small enough one-sided subcritical strip
around `(1/2, 2)`, the selected component admits a regularization model in which
the image of every point outside the set is strictly convex and star-shaped.
This packages the strict convexity of the equal-mass critical surface in the
elliptic-hyperbolic regularization of Liu--Salomao (Theorem 1.12, Section 9)
and its persistence under small changes of `(μ, c)`, as used in Section 10. -/
theorem regularization_model_convex_away_from_saddle_center
    (U : Set Phase) (hU : IsOpen U)
    (hplus : (![1 / 2, 0, 0, 0] : Phase) ∈ U)
    (hminus : (![-(1 / 2), 0, 0, 0] : Phase) ∈ U) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → c < 2 + η → belowFirstCriticalValue μ c →
        ∃ M : RegularizationModel μ c,
          ∀ s ∈ leftEnergyComponent μ c, s ∉ U →
            IsStrictlyConvexStarShapedAt M.modelHamiltonian (M.toModel s) := by sorry

end BirkhoffGlobalSection
