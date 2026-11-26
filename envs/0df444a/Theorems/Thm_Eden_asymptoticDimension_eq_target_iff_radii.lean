-- Prove2me | Theorems.Thm_Eden_asymptoticDimension_eq_target_iff_radii
-- name    : Eden.asymptoticDimension_eq_target_iff_radii
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:53:48.410818+00:00
-- url     : https://prove2.me/theorems/35a9100d-82de-5c17-9719-764e83e24ec9
-- title:
--   Eden: asymptotic Dimension eq target iff radii
-- statement:
--   In the ambient space the maximising radii are exactly one; the fifth
--   coordinate is fixed to zero when the point is restricted to A.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionTable.lean#L113-L118
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionTable.lean#L113-L118

import Definitions.Def_Eden_SpectrumTable
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_DimensionTable
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.asymptoticDimension_eq_target_iff_radii {c : ℝ} (hc : 4 < c) (p : PhaseSpace) :
    asymptoticDimension c p = targetDimension c ↔ radiusSq₁ p = 1 ∧ radiusSq₂ p = 1 := by sorry
