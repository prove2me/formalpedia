-- Prove2me | Theorems.Thm_EdenVerified_p22_descending_radiusPairSpectrum_one_one
-- name    : EdenVerified.p22_descending_radiusPairSpectrum_one_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:50:44.865617+00:00
-- url     : https://prove2.me/theorems/75703926-79a1-434d-820d-4ea43aa91b90
-- title:
--   Eden Verified: p22 descending radius Pair Spectrum one one
-- statement:
--   The Eden Verified construction uses the p22 descending radius Pair Spectrum one one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1745-L1748
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1745-L1748

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p22_descending_radiusPairSpectrum_one_one :
    ∀ {c : ℝ} (hc : 4 < c),
    descending (radiusPairSpectrum c 1 1) = ![2, 2, 0, 0, -c] := by sorry
