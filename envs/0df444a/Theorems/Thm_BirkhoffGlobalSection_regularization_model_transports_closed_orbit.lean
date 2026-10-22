-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_regularization_model_transports_closed_orbit
-- name    : BirkhoffGlobalSection.regularization_model_transports_closed_orbit
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-28T22:24:58.807984+00:00
-- url     : https://prove2.me/theorems/7d6687f2-f46b-4a13-bb16-f5bcbd54a3e6
-- title:
--   Closed orbits transport to the regularization model
-- statement:
--   Closed orbits transport to the model. A closed Levi-Civita solution staying where the regularization is defined is carried by the coordinate map, reparametrized by the positive regularization clock, to a closed model-Hamiltonian solution, with an explicit strictly monotone clock relating the two parametrizations.
--
--   Closing uses the orbit hypothesis; positivity of the new period uses positivity of the time scale. This isolates the orbit-transport mechanics from any winding estimate.
-- source:
--   Closed-orbit transport by the regularization clock and invariance of transverse winding under conformally symplectic coordinate changes with positive time change; see the regularization-coordinate setup of Liu--Salomao, https://arxiv.org/html/2506.17867v2, Section 10.

import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity
import Definitions.Def_BirkhoffGlobalSection_RegularizationModel

namespace BirkhoffGlobalSection

theorem regularization_model_transports_closed_orbit
    (μ c : ℝ) (M : RegularizationModel μ c) (S : Set Phase)
    (x : ℝ → Phase) (T : ℝ)
    (hx : IsPeriodicHamiltonianSolutionIn (leviCivitaHamiltonian μ c)
      (leftEnergyComponent μ c ∩ M.toModel ⁻¹' S) x T) :
    ∃ (y : ℝ → Phase) (T' : ℝ) (σ : ℝ → ℝ),
      IsPeriodicHamiltonianSolutionIn M.modelHamiltonian S y T' ∧
        StrictMono σ ∧ σ 0 = 0 ∧ σ T = T' ∧
        ∀ t : ℝ, y (σ t) = M.toModel (x t) := by sorry

end BirkhoffGlobalSection
