-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_saddle_center_slow_escape_segment
-- name    : BirkhoffGlobalSection.saddle_center_slow_escape_segment
-- status  : Proved
-- author  : @caleb
-- created : 2026-10-01T20:39:34.152898+00:00
-- url     : https://prove2.me/theorems/9691815d-0fc7-45f8-a3b8-8c06a1930be3
-- title:
--   Slow escape segment near the subcritical saddle-centers
-- statement:
--   Let $U \subset \mathbb{R}^4$ be any open neighborhood of both $s_\pm = (\pm \tfrac12, 0, 0, 0)$, and prescribe $L > 0$. There are an open neighborhood $V \subset U$ of both saddle-centers and constants $\varepsilon, \eta > 0$ such that, for
--
--   $$0 < \mu < 1, \qquad |\mu - \tfrac12| < \varepsilon, \qquad c < 2 + \eta, \qquad -c < h_1(\mu),$$
--
--   every closed solution $x$ of the Levi--Civita Hamiltonian on the selected left component meeting $V$ contains a full length-$L$ time interval inside $U$:
--
--   $$x(\mathbb{R}) \cap V \ne \varnothing \quad\Longrightarrow\quad \exists a \in \mathbb{R},\ x([a, a+L]) \subset U.$$
--
--   Here $\mu$ is the mass ratio, $c = -h$ is the energy parameter, $-c < h_1(\mu)$ says the energy lies below the first critical value, and the period of $x$ need not be minimal.
--
--   This is the slow-escape half of the arbitrarily-long-residence statement: trajectories entering the shrunken neighborhood take an arbitrarily long prescribed time to leave the original one, because the vector field is arbitrarily slow near the saddle-centers. The complementary period bound (no short closed orbits) is a separate obligation.
--
--   **Formalization Note** This is the $U_2$ residence-segment paragraph of the proof of Theorem 1.8, specialized to the subcritical side and expressed in Levi--Civita coordinates. No lower bound on the period is asserted here.
-- source:
--   Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2#S7. Proof of Theorem 1.8, paragraphs choosing $U_2$ and asserting arbitrarily large residence time inside the original neighborhood; Section 6.1 saddle-center description; Section 10 subcritical application. Neighborhood-refinement formulation in Levi--Civita coordinates.

import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity

namespace BirkhoffGlobalSection

/-- Slow escape near the two saddle-centers: after shrinking a neighborhood
and the parameter strip, every subcritical periodic orbit meeting the smaller
neighborhood contains a prescribed-length time interval inside the original
one. This isolates the `U₂` residence-segment paragraph of Liu--Salomao,
Section 7, from the period-bound argument. -/
theorem saddle_center_slow_escape_segment
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
            ∃ a : ℝ, ∀ t ∈ Set.Icc a (a + L), x t ∈ U := by sorry

end BirkhoffGlobalSection
