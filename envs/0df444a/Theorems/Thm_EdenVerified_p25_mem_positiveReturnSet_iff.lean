-- Prove2me | Theorems.Thm_EdenVerified_p25_mem_positiveReturnSet_iff
-- name    : EdenVerified.p25_mem_positiveReturnSet_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:35:17.902045+00:00
-- url     : https://prove2.me/theorems/b3ed88e7-a9a9-5ce3-8349-2ced2fefdcbd
-- title:
--   Eden Verified: p25 mem positive Return Set iff
-- statement:
--   The Eden Verified construction uses the p25 mem positive Return Set iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1089-L1093
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1089-L1093

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p25_mem_positiveReturnSet_iff :
    ∀ {c : ℝ} (hc : 0 < c) (p : PhaseSpace),
    p ∈ positiveReturnSet c ↔ p = 0 ∨ p ∈ firstCircle 1 ∨ p ∈ firstCircle 2 ∨
      p ∈ secondCircle 1 ∨ p ∈ secondCircle 2 := by sorry
