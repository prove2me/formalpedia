-- Prove2me | Theorems.Thm_Eden_fderiv_evolution_add
-- name    : Eden.fderiv_evolution_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:37:27.299808+00:00
-- url     : https://prove2.me/theorems/ef299f7d-ccde-4121-9607-e67ad6dd4d14
-- title:
--   Eden: fderiv evolution add
-- statement:
--   The Frechet derivative of the flow satisfies the cocycle law.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorCocycle.lean#L34-L42
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorCocycle.lean#L34-L42

import Definitions.Def_Eden_ExteriorSingularValues
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_ExteriorCocycle
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.fderiv_evolution_add (c : ℝ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (p : PhaseSpace) :
    fderiv ℝ (evolution c (s + t)) p =
      (fderiv ℝ (evolution c t) (evolution c s p)).comp (fderiv ℝ (evolution c s) p) := by sorry
