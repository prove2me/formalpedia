-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_saddle_center_no_short_subcritical_orbits
-- name    : BirkhoffGlobalSection.saddle_center_no_short_subcritical_orbits
-- status  : Proved
-- author  : @caleb
-- created : 2026-10-01T20:39:43.33061+00:00
-- url     : https://prove2.me/theorems/9021982c-15a9-4d9c-977e-ee6fd6d6d93d
-- title:
--   No short subcritical periodic orbits near the saddle-centers
-- statement:
--   Let $U \subset \mathbb{R}^4$ be any open neighborhood of both $s_\pm = (\pm \tfrac12, 0, 0, 0)$, and prescribe $L > 0$. There are an open neighborhood $V \subset U$ of both saddle-centers and constants $\varepsilon, \eta > 0$ such that, for
--
--   $$0 < \mu < 1, \qquad |\mu - \tfrac12| < \varepsilon, \qquad c < 2 + \eta, \qquad -c < h_1(\mu),$$
--
--   every closed solution $x$ of period $T$ of the Levi--Civita Hamiltonian on the selected left component meeting $V$ has period exceeding $L$:
--
--   $$x(\mathbb{R}) \cap V \ne \varnothing \quad\Longrightarrow\quad L < T.$$
--
--   Here $\mu$ is the mass ratio, $c = -h$ is the energy parameter, $-c < h_1(\mu)$ says the energy lies below the first critical value, and the period $T$ need not be minimal.
--
--   This is the period-bound half of the arbitrarily-long-residence statement: short closed orbits cannot accumulate on the saddle-centers because there are no local periodic (Lyapunov) orbits on the subcritical side, so after shrinking the neighborhood every visiting closed orbit is long. The complementary long-residence segment is a separate obligation.
--
--   **Formalization Note** This is the $U_1$ period-bound paragraph of the proof of Theorem 1.8 (the part using the absence of local subcritical Lyapunov orbits), specialized to the subcritical side and expressed in Levi--Civita coordinates. No residence segment is asserted here.
-- source:
--   Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2#S7. Proof of Theorem 1.8, paragraphs choosing $U_1$ and asserting $T > b-a$ via the absence of local subcritical Lyapunov orbits; Section 6.1 saddle-center description; Section 10 subcritical application. Neighborhood-refinement formulation in Levi--Civita coordinates.

import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity

namespace BirkhoffGlobalSection

/-- No short subcritical periodic orbits near the two saddle-centers: after
shrinking a neighborhood and the parameter strip, every subcritical periodic
orbit meeting the smaller neighborhood has period exceeding any prescribed
bound. The strict bound uses the absence of local subcritical Lyapunov
orbits. This isolates the `U₁` period-bound paragraph of Liu--Salomao,
Section 7, from the residence-segment argument. -/
theorem saddle_center_no_short_subcritical_orbits
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
            L < T := by sorry

end BirkhoffGlobalSection
