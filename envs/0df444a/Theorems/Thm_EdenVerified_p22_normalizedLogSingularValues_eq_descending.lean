-- Prove2me | Theorems.Thm_EdenVerified_p22_normalizedLogSingularValues_eq_descending
-- name    : EdenVerified.p22_normalizedLogSingularValues_eq_descending
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:49:02.832174+00:00
-- url     : https://prove2.me/theorems/c12e04f1-4914-420f-b6f3-86c2386cf0bc
-- title:
--   Eden Verified: p22 normalized Log Singular Values eq descending
-- statement:
--   The Eden Verified construction uses the p22 normalized Log Singular Values eq descending property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1675-L1680
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1675-L1680

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p22_normalizedLogSingularValues_eq_descending :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace),
    normalizedLogSingularValues c t p =
      descending (fun i => Real.log (derivativeFactors c t p i) / t) := by sorry
