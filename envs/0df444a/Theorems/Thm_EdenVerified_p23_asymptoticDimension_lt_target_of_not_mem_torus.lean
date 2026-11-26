-- Prove2me | Theorems.Thm_EdenVerified_p23_asymptoticDimension_lt_target_of_not_mem_torus
-- name    : EdenVerified.p23_asymptoticDimension_lt_target_of_not_mem_torus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:51:50.88203+00:00
-- url     : https://prove2.me/theorems/35f9ee88-65de-517c-b1ab-d48b02d05926
-- title:
--   Eden Verified: p23 asymptotic Dimension lt target of not mem torus
-- statement:
--   The Eden Verified construction uses the p23 asymptotic Dimension lt target of not mem torus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1814-L1818
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1814-L1818

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p23_asymptoticDimension_lt_target_of_not_mem_torus :
    ∀ {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ attractor) (hT : p ∉ torus),
    asymptoticDimension c p < targetDimension c := by sorry
