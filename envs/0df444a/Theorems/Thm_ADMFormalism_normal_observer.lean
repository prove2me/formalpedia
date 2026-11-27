-- Prove2me | Theorems.Thm_ADMFormalism_normal_observer
-- name    : ADMFormalism.normal_observer
-- status  : Open
-- author  : @LG
-- created : 2026-11-27T03:06:07.907173+00:00
-- url     : https://prove2.me/theorems/95d319c6-42bc-4689-b865-06f0ca43d6b7
-- title:
--   The Eulerian observers' 4-velocity is a unit normal to the slices
-- statement:
--   The Eulerian observers' 4-velocity - the normalized normal vector (1/N, -N^i/N) - is a unit timelike vector orthogonal to every purely spatial direction.  Formally: the ADM form at (t, x) evaluates on (normalVec D t x, normalVec D t x) to exactly -1, and pairs normalVec with any tangent vector v with v.1 = 0 to exactly 0.  This is the source's statement that the lapse and shift 'describe how each of the leaves Sigma_t of the foliation of spacetime are welded together': the welding is along unit normals.
-- source:
--   Wikipedia, ADM formalism, https://en.wikipedia.org/wiki/ADM_formalism (source of the quoted statements, reproduced verbatim in the definition file) ('there are four Lagrange multipliers: the lapse function, N, and components of shift vector field, N^i. These describe how each of the "leaves" Sigma_t of the foliation of spacetime are welded together')

import Mathlib
import Definitions.Def_ADMFormalism

namespace ADMFormalism

/-! The Eulerian observers' 4-velocity — the normalized normal vector
`(1/N, -N^i/N)` — is a unit timelike vector orthogonal to every purely spatial
direction: the leaves Σ_t are welded together along unit normals. -/

theorem normal_observer (D : ADMFormalism.ADMData) (t : ℝ) (x : ADMFormalism.Spc3) :
    ADMFormalism.admForm D t x (ADMFormalism.normalVec D t x) (ADMFormalism.normalVec D t x) = -1
    ∧ ∀ v : ADMFormalism.Spc4, v.1 = 0 →
        ADMFormalism.admForm D t x (ADMFormalism.normalVec D t x) v = 0 := by
  sorry

end ADMFormalism
