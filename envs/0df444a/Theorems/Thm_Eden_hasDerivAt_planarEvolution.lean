-- Prove2me | Theorems.Thm_Eden_hasDerivAt_planarEvolution
-- name    : Eden.hasDerivAt_planarEvolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:30:13.987537+00:00
-- url     : https://prove2.me/theorems/02b402d0-9597-5df6-9e08-6ac278c3ea42
-- title:
--   Eden: has Deriv At planar Evolution
-- statement:
--   The Eden construction uses the has Deriv At planar Evolution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarDerivative.lean#L24-L31
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarDerivative.lean#L24-L31

import Definitions.Def_Eden_PlanarVectorField
import Definitions.Def_Eden_DerivativeFrames
import Definitions.Def_Eden_PlanarDerivative
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.hasDerivAt_planarEvolution (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PlanarSpace) :
    HasDerivAt (fun τ => planarEvolution Ω τ p)
      (planarVectorField Ω (planarEvolution Ω t p)) t := by sorry
