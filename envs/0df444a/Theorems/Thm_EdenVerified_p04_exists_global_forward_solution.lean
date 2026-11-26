-- Prove2me | Theorems.Thm_EdenVerified_p04_exists_global_forward_solution
-- name    : EdenVerified.p04_exists_global_forward_solution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:31:14.366718+00:00
-- url     : https://prove2.me/theorems/1cda803a-0d1e-4566-ace0-9397b184f841
-- title:
--   Eden Verified: p04 exists global forward solution
-- statement:
--   The Eden Verified construction uses the p04 exists global forward solution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L857-L861
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L857-L861

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p04_exists_global_forward_solution :
    ∀ (c : ℝ) (p : PhaseSpace),
    ∃ f : ℝ → PhaseSpace, f 0 = p ∧
      ∀ t, 0 ≤ t → HasDerivAt f (vectorField c (f t)) t := by sorry
