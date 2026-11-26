-- Prove2me | Theorems.Thm_Eden_derivativeFactors_at_origin
-- name    : Eden.derivativeFactors_at_origin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:42:16.625972+00:00
-- url     : https://prove2.me/theorems/1be459c0-e1fe-4fdb-a73e-19986f6e9876
-- title:
--   Eden: derivative Factors at origin
-- statement:
--   The Eden construction uses the derivative Factors at origin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/StationaryFactors.lean#L56-L62
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/StationaryFactors.lean#L56-L62

import Definitions.Def_Eden_DerivativeDecomposition
import Definitions.Def_Eden_StationaryFactors
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.derivativeFactors_at_origin (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    derivativeFactors c t 0 =
      !₂[Real.exp (-2 * t), Real.exp (-2 * t), Real.exp (-2 * t),
         Real.exp (-2 * t), Real.exp (-c * t)] := by sorry
