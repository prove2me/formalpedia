-- Prove2me | Theorems.Thm_Eden_planarDerivativeY_at_origin
-- name    : Eden.planarDerivativeY_at_origin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:49:52.421246+00:00
-- url     : https://prove2.me/theorems/c6f6f140-967b-4ae6-923e-c89bd838ebd2
-- title:
--   Eden: planar Derivative Y at origin
-- statement:
--   The Eden construction uses the planar Derivative Y at origin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/StationaryFactors.lean#L51-L54
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/StationaryFactors.lean#L51-L54

import Definitions.Def_Eden_DerivativeDecomposition
import Definitions.Def_Eden_StationaryFactors
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.planarDerivativeY_at_origin (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (dx dy : ℝ) :
    planarDerivativeY Ω t 0 0 dx dy =
      Real.exp (-2 * t) * (dx * Real.sin (Ω * t) + dy * Real.cos (Ω * t)) := by sorry
