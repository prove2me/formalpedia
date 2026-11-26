-- Prove2me | Theorems.Thm_Eden_norm_sq_exteriorEvolution_support
-- name    : Eden.norm_sq_exteriorEvolution_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:32:49.621985+00:00
-- url     : https://prove2.me/theorems/2572af6b-3806-5e5c-bc3e-ef32c45d80d8
-- title:
--   Eden: norm sq exterior Evolution support
-- statement:
--   The Eden construction uses the norm sq exterior Evolution support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorLimits.lean#L52-L62
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorLimits.lean#L52-L62

import Definitions.Def_Eden_ExteriorGeometry
import Definitions.Def_Eden_LogarithmicSums
import Definitions.Def_Eden_FactorLimits
import Definitions.Def_Eden_ExteriorLimits
set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden

theorem Eden.norm_sq_exteriorEvolution_support (k : ℕ) (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) (v : ExteriorSpace k) :
    ‖exteriorEvolution k c t p v‖ ^ 2 = ∑ s ∈ exteriorSupport k p v,
      (exteriorFactor k (derivativeFactors c t p) s * exteriorInitialCoordinates k p v s) ^ 2 := by sorry
