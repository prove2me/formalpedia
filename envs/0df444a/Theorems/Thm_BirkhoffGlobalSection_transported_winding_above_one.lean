-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_transported_winding_above_one
-- name    : BirkhoffGlobalSection.transported_winding_above_one
-- status  : Disproved
-- author  : @caleb
-- created : 2026-09-28T22:24:56.141206+00:00
-- url     : https://prove2.me/theorems/43c292d9-aa01-4541-9b80-770948841fe6
-- title:
--   Transverse winding transfers along the transport
-- statement:
--   Transverse winding transfers along the transport. If a model solution with transverse winding above one is the strictly monotone reparametrized image of a Levi-Civita solution, then the Levi-Civita solution also has transverse winding above one.
--
--   The coordinate change is symplectic up to a positive constant and the time change is orientation-preserving, so neither alters transverse rotation counts. This isolates the winding-invariance analysis from the orbit transport.
-- source:
--   Closed-orbit transport by the regularization clock and invariance of transverse winding under conformally symplectic coordinate changes with positive time change; see the regularization-coordinate setup of Liu--Salomao, https://arxiv.org/html/2506.17867v2, Section 10.

import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity
import Definitions.Def_BirkhoffGlobalSection_RegularizationModel

namespace BirkhoffGlobalSection

theorem transported_winding_above_one
    (μ c : ℝ) (M : RegularizationModel μ c) (S : Set Phase)
    (x : ℝ → Phase) (T : ℝ)
    (y : ℝ → Phase) (T' : ℝ) (σ : ℝ → ℝ)
    (hσ : StrictMono σ) (hσ0 : σ 0 = 0) (hσT : σ T = T')
    (hrel : ∀ t : ℝ, y (σ t) = M.toModel (x t))
    (hwind : HasTransverseWindingAboveOne M.modelHamiltonian y T') :
    HasTransverseWindingAboveOne (leviCivitaHamiltonian μ c) x T := by sorry

end BirkhoffGlobalSection
