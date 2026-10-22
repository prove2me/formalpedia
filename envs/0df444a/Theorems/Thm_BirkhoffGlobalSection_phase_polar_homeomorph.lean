-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_phase_polar_homeomorph
-- name    : BirkhoffGlobalSection.phase_polar_homeomorph
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:01:16.680348+00:00
-- url     : https://prove2.me/theorems/cdd7e0ef-ba6e-4f11-ba73-5cdfdfccd756
-- title:
--   Polar homeomorphism of punctured four-dimensional phase space
-- statement:
--   Removing the origin from four-dimensional real phase space yields a space homeomorphic to the product of the unit three-sphere and the strictly positive radial line. The inverse map multiplies a unit direction by its positive radius. This is the topological polar-coordinate change underlying compact radial graphs.
-- source:
--   Standard polar decomposition of finite-dimensional Euclidean space.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem phase_polar_homeomorph :
    ∃ e : {s : Phase // s ≠ (fun _ : Fin 4 => (0 : ℝ))} ≃ₜ
      ({x : Phase // x ∈ unitThreeSphere} × {r : ℝ // 0 < r}),
      ∀ x : {x : Phase // x ∈ unitThreeSphere},
        ∀ r : {r : ℝ // 0 < r},
          ((e.symm (x, r) :
            {s : Phase // s ≠ (fun _ : Fin 4 => (0 : ℝ))}) : Phase) =
            (fun i : Fin 4 => (r : ℝ) * (x : Phase) i) := by sorry

end BirkhoffGlobalSection
