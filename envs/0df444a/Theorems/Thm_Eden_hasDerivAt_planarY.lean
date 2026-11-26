-- Prove2me | Theorems.Thm_Eden_hasDerivAt_planarY
-- name    : Eden.hasDerivAt_planarY
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:03:16.110937+00:00
-- url     : https://prove2.me/theorems/f9fbd47f-df4a-4c1d-af13-698261c109ce
-- title:
--   Eden: has Deriv At planar Y
-- statement:
--   The Eden construction uses the has Deriv At planar Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarFlow.lean#L100-L105
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarFlow.lean#L100-L105

import Definitions.Def_Eden_ScalarCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Eden_PlanarFlow
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.hasDerivAt_planarY (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (x y : ℝ) :
    HasDerivAt (fun τ => planarY Ω τ x y)
      (q (planarX Ω t x y ^ 2 + planarY Ω t x y ^ 2) * planarY Ω t x y +
        Ω * planarX Ω t x y) t := by sorry
