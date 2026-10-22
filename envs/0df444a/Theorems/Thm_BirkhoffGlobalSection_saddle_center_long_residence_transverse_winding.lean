-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_saddle_center_long_residence_transverse_winding
-- name    : BirkhoffGlobalSection.saddle_center_long_residence_transverse_winding
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-28T02:37:41.370757+00:00
-- url     : https://prove2.me/theorems/823831b2-bc4f-46d6-9459-3d6288d739c4
-- title:
--   A long saddle-center segment forces transverse winding above one
-- statement:
--   Write $K_{\mu,c}$ for the Levi–Civita Hamiltonian and $\Sigma_{\mu,c}$ for its selected left component. There are an open neighborhood $U$ of both reference saddles $s_\pm=(\pm\tfrac12,0,0,0)$ and constants $\varepsilon,\eta,L>0$ with the following property. Suppose
--
--   $$
--   0<\mu<1,\qquad |\mu-\tfrac12|<\varepsilon,\qquad c<2+\eta,\qquad -c<h_1(\mu).
--   $$
--
--   For every closed Hamiltonian solution $x$ in $\Sigma_{\mu,c}$ with period $T$, a resident segment satisfying
--
--   $$
--   L<T,\qquad x([a,a+L])\subset U
--   $$
--
--   forces the transverse linearized flow to turn every nonzero transverse tangent vector through more than one full positive turn over $[0,T]$ in the global quaternionic frame.
--
--   This isolates the index estimate from the separate dynamical assertion that sufficiently close visits force long residence.
--
--   **Formalization Note** This is the long-segment consequence of the source's Section 7 argument, expressed directly for the Levi–Civita Hamiltonian. The obligation includes complementary-arc index control, passage from the ambient index to transverse winding, and the change of initial time. It does not assume these conversion results.
-- source:
--   Liu–Salomão, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2#S7. Section 7: Eq. (7.7), Proposition 7.1, and the last two paragraphs of the proof of Theorem 1.8; subcritical application in Section 10. Adaptation of the index argument to Levi–Civita coordinates and the quaternionic winding definition.

import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity

namespace BirkhoffGlobalSection

/-- The index estimate for a closed orbit with a sufficiently long segment
contained in a small saddle-center neighborhood. This isolates the variational
and index-theoretic part of Liu--Salomao, Section 7, from the residence-time
argument. The interval has length strictly less than the period, leaving a
complementary arc whose index loss must also be controlled. -/
theorem saddle_center_long_residence_transverse_winding :
    ∃ U : Set Phase, IsOpen U ∧
      (![1 / 2, 0, 0, 0] : Phase) ∈ U ∧ (![-(1 / 2), 0, 0, 0] : Phase) ∈ U ∧
      ∃ ε η L : ℝ, 0 < ε ∧ 0 < η ∧ 0 < L ∧
        ∀ μ c : ℝ, 0 < μ → μ < 1 →
          |μ - 1 / 2| < ε → c < 2 + η → belowFirstCriticalValue μ c →
          ∀ (x : ℝ → Phase) (T : ℝ),
            IsPeriodicHamiltonianSolutionIn (leviCivitaHamiltonian μ c)
              (leftEnergyComponent μ c) x T →
            L < T →
            (∃ a : ℝ, ∀ t ∈ Set.Icc a (a + L), x t ∈ U) →
            HasTransverseWindingAboveOne (leviCivitaHamiltonian μ c) x T := by sorry

end BirkhoffGlobalSection
