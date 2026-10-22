-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_regularization_model_low_energy_tail
-- name    : BirkhoffGlobalSection.convex_regularization_model_low_energy_tail
-- status  : Proved
-- author  : @caleb
-- created : 2026-10-02T20:19:12.658316+00:00
-- url     : https://prove2.me/theorems/54138533-6cdd-40af-bcf3-540389fe79f6
-- title:
--   Uniform convex regularization model on the low-energy tail
-- statement:
--   There are $\varepsilon > 0$ and a real cutoff $C$ such that, for every mass ratio and energy with
--
--   $$0 < \mu < 1, \qquad |\mu - \tfrac12| < \varepsilon, \qquad C \le c, \qquad -c < h_1(\mu),$$
--
--   the selected Levi--Civita component carries a convex regularization model: smooth symplectic identifications with a model whose energy surface bounds a compact convex body with positive tangential Hessian, plus the positive regularized-to-regularized time change back to the Levi--Civita flow.
--
--   Here $\mu$ is the mass ratio, $c = -h$ is the energy parameter (so $c \to +\infty$ is the very-negative-energy tail), and $-c < h_1(\mu)$ says the energy lies below the first critical value. The same mass radius $\varepsilon$ applies throughout the unbounded tail; only the cutoff $C$ is existential.
--
--   This is the uniform strict convexity for very negative energy: far down the tail the problem is uniformly close to Kepler-like, so one convex model works for all large $c$. It is the analytic core behind rational retrograde pages on the tail; the page construction and quotient descent are separate obligations.
--
--   **Formalization Note** The statement is the tail-uniform analogue of the local convex-model statements, with the two-sided $|c - c_0| < \eta$ window replaced by the one-sided tail $C \le c$. Neither the cutoff value nor the model is prescribed.
-- source:
--   Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2#S10. Section 10, third paragraph (uniform strict convexity for very negative energy). Adapted as a tail-uniform convex regularization model.

import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel

namespace BirkhoffGlobalSection

/-- Uniform convex model on the very-negative-energy tail: a single mass
radius works for all sufficiently large `c`. This is the uniform strict
convexity of Liu--Salomao, Section 10, third paragraph. -/
theorem convex_regularization_model_low_energy_tail :
    ∃ ε C : ℝ, 0 < ε ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → C ≤ c → belowFirstCriticalValue μ c →
        Nonempty (ConvexRegularizationModel μ c) := by sorry

end BirkhoffGlobalSection
