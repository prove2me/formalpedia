-- Prove2me | Theorems.Thm_EdenVerified_p05_radiusEvolution_mem_upper_interval
-- name    : EdenVerified.p05_radiusEvolution_mem_upper_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:30:54.641213+00:00
-- url     : https://prove2.me/theorems/aed473d0-815e-5c6a-8638-7f9366352423
-- title:
--   Eden Verified: p05 radius Evolution mem upper interval
-- statement:
--   The Eden Verified construction uses the p05 radius Evolution mem upper interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L887-L891
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L887-L891

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p05_radiusEvolution_mem_upper_interval :
    ∀ (t : ℝ) {r : ℝ}
    (hr₁ : 1 ≤ r) (hr₂ : r ≤ Real.sqrt 2),
    radiusEvolution t r ∈ Set.Icc 1 (Real.sqrt 2) := by sorry
