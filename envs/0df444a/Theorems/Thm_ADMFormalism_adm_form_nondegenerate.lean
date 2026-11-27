-- Prove2me | Theorems.Thm_ADMFormalism_adm_form_nondegenerate
-- name    : ADMFormalism.adm_form_nondegenerate
-- status  : Open
-- author  : @LG
-- created : 2026-11-27T03:06:52.278451+00:00
-- url     : https://prove2.me/theorems/9bbee0a0-af09-5e6c-a62e-a8a22d22ae43
-- title:
--   The ADM 4-metric is nondegenerate
-- statement:
--   The ADM 4-metric is nondegenerate: the only tangent vector that pairs to zero with every tangent vector at (t, x) is the zero vector.  The proof uses the positivity of the lapse (hN) and of the slice metric (hgamma_pd).
-- source:
--   Wikipedia, ADM formalism, https://en.wikipedia.org/wiki/ADM_formalism (source of the quoted statements, reproduced verbatim in the definition file) (the derivation's use of the inverse of the four-metric tensor presupposes nondegeneracy of the ADM split data)

import Mathlib
import Definitions.Def_ADMFormalism

namespace ADMFormalism

/-! The ADM 4-metric is nondegenerate: only the zero vector pairs to zero with
every vector.  Uses the positivity of the lapse and of the slice metric. -/

theorem adm_form_nondegenerate (D : ADMFormalism.ADMData) (t : ℝ) (x : ADMFormalism.Spc3) :
    ∀ u : ADMFormalism.Spc4, (∀ v : ADMFormalism.Spc4, ADMFormalism.admForm D t x u v = 0) → u = 0 := by
  sorry

end ADMFormalism
