-- Prove2me | Theorems.Thm_Eden_tendsto_log_exterior_coordinate_sq_div
-- name    : Eden.tendsto_log_exterior_coordinate_sq_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:33:00.055922+00:00
-- url     : https://prove2.me/theorems/441e174b-ceeb-4181-997b-36748f228518
-- title:
--   Eden: tendsto log exterior coordinate sq div
-- statement:
--   The Eden construction uses the tendsto log exterior coordinate sq div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorLimits.lean#L64-L76
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorLimits.lean#L64-L76

import Definitions.Def_Eden_ExteriorGeometry
import Definitions.Def_Eden_LogarithmicSums
import Definitions.Def_Eden_FactorLimits
import Definitions.Def_Eden_ExteriorLimits
set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden

theorem Eden.tendsto_log_exterior_coordinate_sq_div (k : ℕ) (c : ℝ) (p : PhaseSpace)
    (s : ExteriorIndex k) {a : ℝ} (ha : a ≠ 0) :
    Tendsto (fun t => Real.log ((exteriorFactor k (derivativeFactors c t p) s * a) ^ 2) / t)
      atTop (𝓝 (2 * exteriorRate k c p s)) := by sorry
