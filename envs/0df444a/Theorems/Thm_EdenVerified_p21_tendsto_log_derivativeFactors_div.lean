-- Prove2me | Theorems.Thm_EdenVerified_p21_tendsto_log_derivativeFactors_div
-- name    : EdenVerified.p21_tendsto_log_derivativeFactors_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:49:11.552359+00:00
-- url     : https://prove2.me/theorems/94950cad-31d0-41e1-8ec8-555dd3b702dc
-- title:
--   Eden Verified: p21 tendsto log derivative Factors div
-- statement:
--   The Eden Verified construction uses the p21 tendsto log derivative Factors div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1664-L1668
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1664-L1668

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p21_tendsto_log_derivativeFactors_div :
    ∀ (c : ℝ) (p : PhaseSpace) (i : Fin 5),
    Tendsto (fun t => Real.log (derivativeFactors c t p i) / t) atTop
      (𝓝 (factorExponents c p i)) := by sorry
