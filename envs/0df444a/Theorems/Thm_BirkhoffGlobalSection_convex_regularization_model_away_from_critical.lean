-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_regularization_model_away_from_critical
-- name    : BirkhoffGlobalSection.convex_regularization_model_away_from_critical
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-02T14:42:37.14499+00:00
-- url     : https://prove2.me/theorems/c28bafd3-c8e0-48f0-a5a5-35839cc0371b
-- title:
--   Convex regularization near equal masses, uniformly away from the critical energy
-- statement:
--   For every $\eta>0$ there is a mass radius $\varepsilon>0$, uniform in the energy, such that whenever
--
--   $$0<\mu<1,\qquad |\mu-\tfrac12|<\varepsilon,\qquad c\ge2+\eta,\qquad -c<h_1(\mu),$$
--
--   the selected Levi-Civita component admits a convex regularization model (`ConvexRegularizationModel μ c`).
--
--   This merges `convex_regularization_model_local_subcritical` (windows around each $c_0>2$) with the very-negative-energy regime into one statement. Only the near-critical strip $c<2+\eta$ is left out, where Liu--Salomão use dynamical convexity instead (their Remark 9.5 shows convexity fails there for $\mu\ne\tfrac12$).
--
--   **Intended proof.**
--   - Use the explicit elliptic-hyperbolic model (`eh_left_regularization_local_subcritical`, Proved).
--   - Rescale positions $x=X/\sqrt c$ and set $u=1/c$. The rescaled Hamiltonian extends continuously, with its derivatives, to $u=0$. There the zero level is the ellipsoid $\tfrac12|y|^2+\tfrac14|X|^2=1-\mu$, which is strictly convex for every $\mu$.
--   - Strict convexity at $\mu=\tfrac12$ for every $c>2$: star-shapedness is `eh_half_mass_star_shaped` (Proved), and the tangential Hessian is `eh_half_mass_tangential_hessian` (Liu--Salomão Theorem 9.4(ii)).
--   - Compactness of $u\in[0,1/(2+\eta)]$, with the tube lemma of `BirkhoffGlobalSection_EHConvexPerturbation`, gives the uniform mass radius.
-- source:
--   Liu--Salomao, https://arxiv.org/html/2506.17867v2#S10, third paragraph (open neighborhood of {1/2} x (-infinity,-2) on which the regularized components are strictly convex, including uniform strict convexity for very negative energy); Theorems 1.12 and 9.4(ii). Uniform-in-energy form with the u = 1/c compactification constructed here.

import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel

namespace BirkhoffGlobalSection

/-- Convex regularization away from the critical energy, uniformly in the energy:
for every `η > 0` there is one mass radius `ε` such that every subcritical energy
`c ≥ 2 + η` with `|μ - 1/2| < ε` admits a convex regularization model. -/
theorem convex_regularization_model_away_from_critical (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → 2 + η ≤ c → belowFirstCriticalValue μ c →
        Nonempty (ConvexRegularizationModel μ c) := by sorry

end BirkhoffGlobalSection
