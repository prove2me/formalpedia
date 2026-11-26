-- Prove2me | Theorems.Thm_EdenVerified_p11_rates_at_stationary_radii
-- name    : EdenVerified.p11_rates_at_stationary_radii
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:33:48.195229+00:00
-- url     : https://prove2.me/theorems/6c766ecf-acdb-52b1-b774-35581477d547
-- title:
--   Eden Verified: p11 rates at stationary radii
-- statement:
--   The Eden Verified construction uses the p11 rates at stationary radii property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1033-L1037
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1033-L1037

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p11_rates_at_stationary_radii :
    radialRate 0 = -2 ∧ tangentialRate 0 = -2 ∧
    radialRate 1 = 2 ∧ tangentialRate 1 = 0 ∧
    radialRate 2 = -4 ∧ tangentialRate 2 = 0 := by sorry
