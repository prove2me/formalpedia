-- Prove2me | Theorems.Thm_EdenVerified_p26_normalizedLogSingularValues_outer_circle
-- name    : EdenVerified.p26_normalizedLogSingularValues_outer_circle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:37:36.92744+00:00
-- url     : https://prove2.me/theorems/99a93705-6e2c-49e3-b8bd-9070a039c2b1
-- title:
--   Eden Verified: p26 normalized Log Singular Values outer circle
-- statement:
--   The Eden Verified construction uses the p26 normalized Log Singular Values outer circle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1139-L1143
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1139-L1143

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p26_normalizedLogSingularValues_outer_circle :
    ∀ {c t : ℝ} (hc : 4 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ firstCircle 2 ∨ p ∈ secondCircle 2),
    normalizedLogSingularValues c t p = ![0, -2, -2, -4, -c] := by sorry
