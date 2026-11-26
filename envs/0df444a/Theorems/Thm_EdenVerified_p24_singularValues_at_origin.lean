-- Prove2me | Theorems.Thm_EdenVerified_p24_singularValues_at_origin
-- name    : EdenVerified.p24_singularValues_at_origin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:34:09.375794+00:00
-- url     : https://prove2.me/theorems/83f02aba-7fb0-5eac-b5ea-0b08457490c3
-- title:
--   Eden Verified: p24 singular Values at origin
-- statement:
--   The Eden Verified construction uses the p24 singular Values at origin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1046-L1051
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1046-L1051

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p24_singularValues_at_origin :
    ∀ {c t : ℝ} (hc : 2 ≤ c) (ht : 0 ≤ t),
    (fun i : Fin 5 => (fderiv ℝ (evolution c t) 0).toLinearMap.singularValues i) =
      ![Real.exp (-2 * t), Real.exp (-2 * t), Real.exp (-2 * t),
        Real.exp (-2 * t), Real.exp (-c * t)] := by sorry
