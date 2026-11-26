-- Prove2me | Theorems.Thm_Eden_fderiv_evolution_bijective
-- name    : Eden.fderiv_evolution_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:18:10.648796+00:00
-- url     : https://prove2.me/theorems/625ca604-6d1b-4f89-b786-ae16bb2e2d85
-- title:
--   Eden: fderiv evolution bijective
-- statement:
--   The derivative is invertible at every finite nonnegative time.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DerivativeDecomposition.lean#L101-L109
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DerivativeDecomposition.lean#L101-L109

import Definitions.Def_Eden_DerivativeFrames
import Definitions.Def_Eden_DerivativeDecomposition
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.fderiv_evolution_bijective (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    Function.Bijective (fderiv ℝ (evolution c t) p) := by sorry
