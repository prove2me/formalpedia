-- Prove2me | Theorems.Thm_Eden_hasDerivAt_planarX
-- name    : Eden.hasDerivAt_planarX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:02:58.307814+00:00
-- url     : https://prove2.me/theorems/df29d2b3-8884-5375-9f36-2ebd028b45eb
-- title:
--   Eden: has Deriv At planar X
-- statement:
--   The Eden construction uses the has Deriv At planar X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarFlow.lean#L79-L84
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarFlow.lean#L79-L84

import Definitions.Def_Eden_ScalarCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Eden_PlanarFlow
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.hasDerivAt_planarX (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (x y : ℝ) :
    HasDerivAt (fun τ => planarX Ω τ x y)
      (q (planarX Ω t x y ^ 2 + planarY Ω t x y ^ 2) * planarX Ω t x y -
        Ω * planarY Ω t x y) t := by sorry
