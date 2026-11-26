-- Prove2me | Theorems.Thm_EdenVerified_p26_normalizedLogSingularValues_unit_circle
-- name    : EdenVerified.p26_normalizedLogSingularValues_unit_circle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:37:35.932576+00:00
-- url     : https://prove2.me/theorems/7034c736-0c15-47d8-975e-37594e341ef5
-- title:
--   Eden Verified: p26 normalized Log Singular Values unit circle
-- statement:
--   The Eden Verified construction uses the p26 normalized Log Singular Values unit circle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1133-L1137
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1133-L1137

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p26_normalizedLogSingularValues_unit_circle :
    ∀ {c t : ℝ} (hc : 4 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ firstCircle 1 ∨ p ∈ secondCircle 1),
    normalizedLogSingularValues c t p = ![2, 0, -2, -2, -c] := by sorry
