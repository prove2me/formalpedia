-- Prove2me | Theorems.Thm_ADMFormalism_adm_metric_minkowski_congruence
-- name    : ADMFormalism.adm_metric_minkowski_congruence
-- status  : Open
-- author  : @LG
-- created : 2026-11-27T03:07:30.839098+00:00
-- url     : https://prove2.me/theorems/453c3f26-33ae-441a-a3f0-934556ff90a3
-- title:
--   The ADM 4-metric is congruent to the Minkowski form (goal)
-- statement:
--   Goal: at every base event (t, x), the ADM 4-metric is congruent to the flat Minkowski form of signature (-,+,+,+): there exists a linear equivalence L of Spc4 such that for every tangent vector u, admForm D t x (L u) (L u) = -(u^0)^2 + sum_i (u^i)^2.  In other words, the ADM data defines a Lorentzian metric - the premise on which the formalism's constraints and evolution equations rest.  Proof idea: the shear v |-> (v^0, v^i + v^0 N^i) reduces the form to the block-diagonal shape -N^2 dt^2 + gamma; the slice metric is positive definite, so its LDL decomposition (LDL.lower_conj_diag in Mathlib) factors gamma as L D L^T with positive diagonal D, and scaling by sqrt(D) and by N produces the Minkowski form.
-- source:
--   Wikipedia, ADM formalism, https://en.wikipedia.org/wiki/ADM_formalism (source of the quoted statements, reproduced verbatim in the definition file) ('The ADM split denotes the separation of the spacetime metric into three spatial components and one temporal component (foliation)'); R. Arnowitt, S. Deser, C. W. Misner, The dynamics of general relativity (1959/1962); Mathlib LDL decomposition of positive definite matrices (Mathlib/Analysis/Matrix/LDL.lean)

import Mathlib
import Definitions.Def_ADMFormalism

namespace ADMFormalism

/-! The goal: the ADM 4-metric at every base event is congruent to the flat
Minkowski form of signature `(-,+,+,+)` — the ADM data defines a Lorentzian
metric, the premise on which the formalism's constraints and evolution
equations rest.  Tractable via the shear `v ↦ (v.1, v.2 + v.1 N^i)` reducing to
the block-diagonal form `-N² dt² + γ`, then the LDL decomposition of the
positive definite slice metric (`LDL.lower_conj_diag`) with the positive
diagonal `D` giving `√D`. -/

theorem adm_metric_minkowski_congruence (D : ADMFormalism.ADMData) (t : ℝ) (x : ADMFormalism.Spc3) :
    ∃ L : ADMFormalism.Spc4 ≃ₗ[ℝ] ADMFormalism.Spc4, ∀ u : ADMFormalism.Spc4,
      ADMFormalism.admForm D t x (L u) (L u) = -(u.1) ^ 2 + ∑ i, (u.2 i) ^ 2 := by
  sorry

end ADMFormalism
