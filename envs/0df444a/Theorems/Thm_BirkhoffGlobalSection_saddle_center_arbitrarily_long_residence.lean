-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_saddle_center_arbitrarily_long_residence
-- name    : BirkhoffGlobalSection.saddle_center_arbitrarily_long_residence
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-28T02:37:48.105771+00:00
-- url     : https://prove2.me/theorems/0e2e2205-53b3-480c-a02b-6657f0d1c4b7
-- title:
--   Arbitrarily long residence near the subcritical saddle-centers
-- statement:
--   Let $U\subset\mathbb R^4$ be any open neighborhood of both $s_\pm=(\pm\tfrac12,0,0,0)$, and prescribe $L>0$. There are an open neighborhood $V\subset U$ of both saddles and constants $\varepsilon,\eta>0$ such that, for
--
--   $$
--   0<\mu<1,\qquad |\mu-\tfrac12|<\varepsilon,\qquad c<2+\eta,\qquad -c<h_1(\mu),
--   $$
--
--   any closed solution $x$ of the Levi–Civita Hamiltonian on the selected left component with period $T$ satisfies
--
--   $$
--   x(\mathbb R)\cap V\ne\varnothing
--   \quad\Longrightarrow\quad
--   L<T\ \text{ and }\ \exists a\in\mathbb R,\ x([a,a+L])\subset U.
--   $$
--
--   The period need not be minimal. This supplies a long resident segment without assuming anything about the variational flow or its winding.
--
--   **Formalization Note** This is the slow-passage assertion in the proof of Theorem 1.8, specialized to the subcritical side as in Section 10 and expressed in Levi–Civita coordinates. The strict period bound includes the exclusion of local subcritical periodic orbits; mere smallness of the vector field is not the full assertion.
-- source:
--   Liu–Salomão, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2#S7. Proof of Theorem 1.8, paragraphs choosing U_1 and U_2 and asserting T > b-a with arbitrarily large residence time; Section 6.1 saddle-center description; Section 10 subcritical application. Neighborhood-refinement formulation in Levi–Civita coordinates.

import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity

namespace BirkhoffGlobalSection

/-- Slow passage near the two saddle-centers: after shrinking a neighborhood
and the parameter strip, every subcritical periodic orbit meeting the smaller
neighborhood has a prescribed-length segment inside the original one. The
strict period bound uses the absence of local subcritical Lyapunov orbits. -/
theorem saddle_center_arbitrarily_long_residence
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
            L < T ∧ ∃ a : ℝ, ∀ t ∈ Set.Icc a (a + L), x t ∈ U := by sorry

end BirkhoffGlobalSection
