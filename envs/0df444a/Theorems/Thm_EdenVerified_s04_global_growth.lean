-- Prove2me | Theorems.Thm_EdenVerified_s04_global_growth
-- name    : EdenVerified.s04_global_growth
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:22:12.037054+00:00
-- url     : https://prove2.me/theorems/3d95f757-2f27-5f2c-b18f-0a36f0855f47
-- title:
--   Eden Verified: s04 global growth
-- statement:
--   Finite spatial suprema, real-time subadditivity and an explicit linear bound.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L200-L213
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L200-L213

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.s04_global_growth (c : ℝ) (hc : 4 < c) (k : ℕ) (hk : k ≤ 5) :
    (∀ t : ℝ, 0 ≤ t → (integerGrowthValues c k t).Nonempty ∧
      BddAbove (integerGrowthValues c k t) ∧ 0 < supremumSingularProduct c k t) ∧
    globalLogGrowth c k 0 = 0 ∧
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      globalLogGrowth c k (s+t) ≤ globalLogGrowth c k s + globalLogGrowth c k t) ∧
    0 ≤ (k : ℝ) * c ∧
    (∀ t : ℝ, 0 ≤ t → |globalLogGrowth c k t| ≤ ((k : ℝ) * c) * t) := by sorry
