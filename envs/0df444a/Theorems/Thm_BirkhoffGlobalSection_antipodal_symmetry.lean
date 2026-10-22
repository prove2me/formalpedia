-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_antipodal_symmetry
-- name    : BirkhoffGlobalSection.antipodal_symmetry
-- status  : Proved
-- author  : @Yivy Yu
-- created : 2026-09-12T15:08:05.924124+00:00
-- url     : https://prove2.me/theorems/ca17f3a8-68e8-4adf-8ea4-d6233d3acaa6
-- title:
--   Antipodal symmetry of the Levi-Civita component
-- statement:
--   Let $0<\mu<1$ and $-c<h_1(\mu)$. The totalized Levi-Civita formula is even, and on the selected subcritical component the antipodal map is invariant and free:
--
--   $$
--   K_{\mu,c}(-s)=K_{\mu,c}(s),
--   \qquad
--   -s\in\Sigma_{\mu,c}\iff s\in\Sigma_{\mu,c},
--   \qquad
--   s\neq -s\quad(s\in\Sigma_{\mu,c}).
--   $$
--
--   The Hamiltonian equality is an algebraic consequence of the displayed formula, including Lean's totalized extension at the excluded singular locus. Invariance and freeness are the deck-action properties on the physical subcritical component used in Joung--van Koert Proposition 2.4; equation (2.4) names the involution.
-- source:
--   Joung--van Koert, equation (2.4) and Proposition 2.4, https://arxiv.org/abs/2407.19159v3.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- Algebraic evenness of the totalized Levi-Civita formula, together with the
free component-preserving antipodal deck action in the physical subcritical
regime of Joung--van Koert, Proposition 2.4. -/
theorem antipodal_symmetry (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : belowFirstCriticalValue μ c) :
    (∀ s : Phase,
      leviCivitaHamiltonian μ c (-s) = leviCivitaHamiltonian μ c s) ∧
    IsAntipodallyInvariantComponent μ c ∧
    IsAntipodallyFreeComponent μ c := by sorry

end BirkhoffGlobalSection
