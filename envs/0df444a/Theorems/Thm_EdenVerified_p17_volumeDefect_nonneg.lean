-- Prove2me | Theorems.Thm_EdenVerified_p17_volumeDefect_nonneg
-- name    : EdenVerified.p17_volumeDefect_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:47:22.840554+00:00
-- url     : https://prove2.me/theorems/b44442b8-30f7-4f51-9c18-ef38b0e46373
-- title:
--   Eden Verified: p17 volume Defect nonneg
-- statement:
--   The Eden Verified construction uses the p17 volume Defect nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1540-L1543
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1540-L1543

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p17_volumeDefect_nonneg :
    ∀ {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace),
    0 ≤ volumeDefect t p := by sorry
