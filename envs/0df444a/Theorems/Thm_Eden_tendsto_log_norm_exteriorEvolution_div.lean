-- Prove2me | Theorems.Thm_Eden_tendsto_log_norm_exteriorEvolution_div
-- name    : Eden.tendsto_log_norm_exteriorEvolution_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:32:53.116989+00:00
-- url     : https://prove2.me/theorems/7b6351c3-5d0a-4d86-9d3b-aed142c3ac8c
-- title:
--   Eden: tendsto log norm exterior Evolution div
-- statement:
--   Every fixed nonzero exterior vector has an ordinary logarithmic growth
--   limit. Its value is the greatest sum of block exponents with a nonzero
--   initial coordinate; time ranges over all reals tending to infinity.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorLimits.lean#L81-L113
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorLimits.lean#L81-L113

import Definitions.Def_Eden_ExteriorGeometry
import Definitions.Def_Eden_LogarithmicSums
import Definitions.Def_Eden_FactorLimits
import Definitions.Def_Eden_ExteriorLimits
set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden

theorem Eden.tendsto_log_norm_exteriorEvolution_div {k : ℕ} (c : ℝ) (p : PhaseSpace)
    {v : ExteriorSpace k} (hv : v ≠ 0) :
    Tendsto (fun t => Real.log ‖exteriorEvolution k c t p v‖ / t) atTop
      (𝓝 ((exteriorSupport k p v).sup' (exteriorSupport_nonempty p hv) (exteriorRate k c p))) := by sorry
