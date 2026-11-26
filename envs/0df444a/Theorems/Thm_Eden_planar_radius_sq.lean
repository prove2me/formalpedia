-- Prove2me | Theorems.Thm_Eden_planar_radius_sq
-- name    : Eden.planar_radius_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:06:07.173051+00:00
-- url     : https://prove2.me/theorems/1bdba184-68b9-569d-bb10-b7ec465fd4b7
-- title:
--   Eden: planar radius sq
-- statement:
--   The Eden construction uses the planar radius sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarFlow.lean#L58-L62
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarFlow.lean#L58-L62

import Definitions.Def_Eden_ScalarCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Eden_PlanarFlow
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.planar_radius_sq (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (x y : ℝ) :
    planarX Ω t x y ^ 2 + planarY Ω t x y ^ 2 =
      squaredRadiusEvolution t (x ^ 2 + y ^ 2) := by sorry
