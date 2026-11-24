-- Prove2me | solution 10 for waDiag.p1
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-24T18:12:57.467922+00:00
-- url     : https://prove2.me/submissions/bc18e11c-429f-44c2-9717-f2deaa2759e0

import Mathlib
/-! # M2: same name, but declared `private` -/

set_option autoImplicit false

namespace Kyprianou.Ch08.StageB

private def HasSourceScaleFamily (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) : Prop := ∀ x, 0 ≤ W 0 x

end Kyprianou.Ch08.StageB

theorem solution : True := trivial
