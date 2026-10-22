-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_regularization_model_local_subcritical
-- name    : BirkhoffGlobalSection.convex_regularization_model_local_subcritical
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-27T01:35:44.765271+00:00
-- url     : https://prove2.me/theorems/fe191fb6-8e08-4bb9-9853-8520b15a60c5
-- title:
--   Local convex regularization near a fixed equal-mass subcritical energy
-- statement:
--   Fix a regular equal-mass energy parameter $c_0>2$. There exist positive numbers $\varepsilon,\eta$ such that
--
--   $$
--   0<\mu<1,\quad |\mu-\tfrac12|<\varepsilon,\quad |c-c_0|<\eta,\quad -c<h_1(\mu)
--   \quad\Longrightarrow\quad
--   \text{a convex regularization model of }\Sigma_{\mu,c}\text{ exists}.
--   $$
--
--   The model includes a smooth equivariant coordinate identification with the boundary of a compact convex body, a regular defining Hamiltonian with positive tangential Hessian, conformal symplectic compatibility, and a continuous positive regularized time factor. In particular, this does not assert positive tangential Hessian for the Levi-Civita Hamiltonian itself.
--
--   This is the geometric local-persistence obligation in the reduction of lifted retrograde page existence. It adapts the fixed-energy convexity argument of Liu--Salomao to the platform's Levi-Civita component. The identification across collision and the positivity of the clock are part of this open assertion; they are not supplied merely by a sphere homeomorphism. It contains no page-existence or return conclusion.
--
--   **Formalization Note.** Existence is `Nonempty (ConvexRegularizationModel μ c)`. This transport formulation is a new lemma for the decomposition, not a verbatim assertion in the paper.
-- source:
--   Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2, Section 4 (elliptic-hyperbolic regularization), Theorem 1.12, and Section 10 (local persistence of convexity). This is an explicit transport interface for the Prove2Me Levi-Civita model, rather than a definition quoted verbatim from the paper.

import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel

namespace BirkhoffGlobalSection

/-- Local convexity in an alternative regularization, including the smooth
symplectic identification and positive time change back to the LC model. -/
theorem convex_regularization_model_local_subcritical
    (c₀ : ℝ) (hc₀ : 2 < c₀) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → |c - c₀| < η → belowFirstCriticalValue μ c →
        Nonempty (ConvexRegularizationModel μ c) := by sorry

end BirkhoffGlobalSection
