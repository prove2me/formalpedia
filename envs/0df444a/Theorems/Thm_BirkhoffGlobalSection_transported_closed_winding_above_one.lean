-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_transported_closed_winding_above_one
-- name    : BirkhoffGlobalSection.transported_closed_winding_above_one
-- status  : Disproved
-- author  : @caleb
-- created : 2026-09-30T00:15:21.946283+00:00
-- url     : https://prove2.me/theorems/dfcacff9-0d37-4bf1-b879-766d5b764e1f
-- title:
--   Closed-orbit winding transfers along the transport
-- statement:
--   Transverse winding transfers along the transport, for genuine closed orbits. If $x$ is a closed Levi-Civita solution in the preimage set, $y$ is a closed model solution with transverse winding above one, and $y$ is the strictly monotone reparametrized image of $x$, then $x$ also has transverse winding above one.
--
--   The coordinate change is symplectic up to a positive constant and the time change is orientation-preserving, so neither alters transverse rotation counts.
--
--   **Formalization Note.** The closed-orbit hypotheses on both sides are essential: an earlier unconstrained version is false, since nothing then ties $x$ to the flow and an empty-component model with zero Hamiltonian makes the winding hypothesis vacuous while the conclusion fails.
-- source:
--   Corrected winding-transfer lemma: closed-orbit hypotheses on both sides, blocking vacuous-instantiation counterexamples. Transport mechanism as in Liu--Salomao, https://arxiv.org/html/2506.17867v2, Section 10.

import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity
import Definitions.Def_BirkhoffGlobalSection_RegularizationModel

namespace BirkhoffGlobalSection

theorem transported_closed_winding_above_one
    (μ c : ℝ) (M : RegularizationModel μ c) (S : Set Phase)
    (x : ℝ → Phase) (T : ℝ)
    (hx : IsPeriodicHamiltonianSolutionIn (leviCivitaHamiltonian μ c)
      (leftEnergyComponent μ c ∩ M.toModel ⁻¹' S) x T)
    (y : ℝ → Phase) (T' : ℝ)
    (hy : IsPeriodicHamiltonianSolutionIn M.modelHamiltonian S y T')
    (σ : ℝ → ℝ)
    (hσ : StrictMono σ) (hσ0 : σ 0 = 0) (hσT : σ T = T')
    (hrel : ∀ t : ℝ, y (σ t) = M.toModel (x t))
    (hwind : HasTransverseWindingAboveOne M.modelHamiltonian y T') :
    HasTransverseWindingAboveOne (leviCivitaHamiltonian μ c) x T := by sorry

end BirkhoffGlobalSection
