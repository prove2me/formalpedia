-- Prove2me | Theorems.Thm_Eden_norm_sq_exteriorEvolution
-- name    : Eden.norm_sq_exteriorEvolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:27:29.845805+00:00
-- url     : https://prove2.me/theorems/5db06723-46bd-552e-9327-4603737572e2
-- title:
--   Eden: norm sq exterior Evolution
-- statement:
--   The full norm formula for every fixed exterior vector under the derivative; its nonnegative terms retain all coefficients and multiplicities.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorGeometry.lean#L106-L115
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorGeometry.lean#L106-L115

import Definitions.Def_Eden_DerivativeDecomposition
import Mathlib.Analysis.InnerProductSpace.ExteriorPower
import Definitions.Def_Eden_ExteriorGeometry
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.norm_sq_exteriorEvolution (k : ℕ) (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) (v : ExteriorSpace k) :
    ‖exteriorEvolution k c t p v‖ ^ 2 = ∑ s : ExteriorIndex k,
      (exteriorFactor k (derivativeFactors c t p) s * exteriorInitialCoordinates k p v s) ^ 2 := by sorry
