-- Prove2me | Theorems.Thm_ADMFormalism_slices_are_spacelike
-- name    : ADMFormalism.slices_are_spacelike
-- status  : Open
-- author  : @LG
-- created : 2026-11-27T03:05:40.821255+00:00
-- url     : https://prove2.me/theorems/5d32023f-112d-5494-9bfd-edfcde5dcb10
-- title:
--   The slices Sigma_t are spacelike with induced metric gamma
-- statement:
--   The slices Sigma_t are spacelike and their induced metric is the slice metric gamma (the source's g_ij = (4)g_ij).  Formally: for any tangent vector u with no time component (u.1 = 0), the ADM form at (t, x) evaluates on u, u to exactly the slice pairing sum_{i,j} gamma_ij u^i u^j, and this value is strictly positive whenever the spatial part of u is nonzero - so the foliation of spacetime is into spacelike surfaces with induced metric gamma.
-- source:
--   Wikipedia, ADM formalism, https://en.wikipedia.org/wiki/ADM_formalism (source of the quoted statements, reproduced verbatim in the definition file) ('The formalism supposes that spacetime is foliated into a family of spacelike surfaces'; 'The metric of the three-dimensional slices g_ij = (4)g_ij')

import Mathlib
import Definitions.Def_ADMFormalism

namespace ADMFormalism

/-! The slices Σ_t are spacelike with induced metric `γ` (the source's
`g_ij = (4)g_ij`): on tangent vectors with no time component the ADM form
restricts to the slice pairing `γ_ij a^i b^j`, which is positive for nonzero
spatial vectors. -/

theorem slices_are_spacelike (D : ADMFormalism.ADMData) (t : ℝ) (x : ADMFormalism.Spc3)
    (u : ADMFormalism.Spc4) (hu : u.1 = 0) :
    ADMFormalism.admForm D t x u u
      = ∑ i, ∑ j, D.γ t x i j * u.2 i * u.2 j
    ∧ (u.2 ≠ 0 → 0 < ADMFormalism.admForm D t x u u) := by
  sorry

end ADMFormalism
