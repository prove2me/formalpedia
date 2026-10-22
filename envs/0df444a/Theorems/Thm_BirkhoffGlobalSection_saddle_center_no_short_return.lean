-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_saddle_center_no_short_return
-- name    : BirkhoffGlobalSection.saddle_center_no_short_return
-- status  : Proved
-- author  : @caleb
-- created : 2026-10-01T21:05:24.554704+00:00
-- url     : https://prove2.me/theorems/8a589db0-2ee3-4e31-b21b-4f5d93fbe1bc
-- title:
--   No short return after visiting the saddle-centers
-- statement:
--   Let $U \subset \mathbb{R}^4$ be any open neighborhood of both $s_\pm = (\pm \tfrac12, 0, 0, 0)$, and prescribe $L > 0$. There are an open neighborhood $V \subset U$ of both saddle-centers and constants $\varepsilon, \eta > 0$ such that, for
--
--   $$0 < \mu < 1, \qquad |\mu - \tfrac12| < \varepsilon, \qquad c < 2 + \eta, \qquad -c < h_1(\mu),$$
--
--   no trajectory of the Levi--Civita Hamiltonian on the selected left component that meets $V$ returns to a visited point within any prescribed positive time up to $L$:
--
--   $$x(s) \in V \quad\Longrightarrow\quad x(s + d) \ne x(s) \qquad (0 < d \le L).$$
--
--   Here $\mu$ is the mass ratio, $c = -h$ is the energy parameter, and $-c < h_1(\mu)$ says the energy lies below the first critical value.
--
--   This is the injectivity half of the period bound near the saddle-centers: during the slow passage the orbit cannot repeat, so a closed orbit visiting $V$ must have period exceeding $L$. Combined with shift-invariance of anchored-periodic solutions, it yields the strict period bound; the complementary long-residence segment is a separate obligation.
--
--   **Formalization Note** This is the injectivity content of the $T > b-a$ paragraph of the proof of Theorem 1.8, specialized to the subcritical side and expressed in Levi--Civita coordinates. No lower bound on the period itself is asserted here.
-- source:
--   Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2#S7. Proof of Theorem 1.8, paragraphs asserting $T > b-a$ (injectivity during the slow passage); Section 6.1 saddle-center description; Section 10 subcritical application. Neighborhood-refinement formulation in Levi--Civita coordinates.

import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity

namespace BirkhoffGlobalSection

/-- No short return after visiting the saddle-centers: after shrinking a
neighborhood and the parameter strip, no subcritical trajectory meeting the
smaller neighborhood comes back to a visited point within any prescribed
positive time up to `L`. This is the injectivity half of the `T > b - a`
paragraph of Liu--Salomao, Section 7: during the slow passage the orbit
cannot repeat. The period bound follows by combining this with
shift-invariance of anchored-periodic solutions. -/
theorem saddle_center_no_short_return
    (U : Set Phase) (hU : IsOpen U)
    (hplus : (![1 / 2, 0, 0, 0] : Phase) ∈ U)
    (hminus : (![-(1 / 2), 0, 0, 0] : Phase) ∈ U)
    (L : ℝ) (hL : 0 < L) :
    ∃ V : Set Phase, IsOpen V ∧ V ⊆ U ∧
      (![1 / 2, 0, 0, 0] : Phase) ∈ V ∧ (![-(1 / 2), 0, 0, 0] : Phase) ∈ V ∧
      ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
        ∀ μ c : ℝ, 0 < μ → μ < 1 →
          |μ - 1 / 2| < ε → c < 2 + η → belowFirstCriticalValue μ c →
          ∀ (x : ℝ → Phase) (T : ℝ),
            IsPeriodicHamiltonianSolutionIn (leviCivitaHamiltonian μ c)
              (leftEnergyComponent μ c) x T →
            (∃ t : ℝ, x t ∈ V) →
            ∀ s : ℝ, x s ∈ V → ∀ d : ℝ, 0 < d → d ≤ L →
              x (s + d) ≠ x s := by sorry

end BirkhoffGlobalSection
