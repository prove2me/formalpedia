-- Prove2me | Theorems.Thm_EdenVerified_p22_descending_radiusPairSpectrum_zero_one
-- name    : EdenVerified.p22_descending_radiusPairSpectrum_zero_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:50:04.915154+00:00
-- url     : https://prove2.me/theorems/a1b4eb5e-4299-501b-b83f-14473f48b012
-- title:
--   Eden Verified: p22 descending radius Pair Spectrum zero one
-- statement:
--   The Eden Verified construction uses the p22 descending radius Pair Spectrum zero one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1735-L1738
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1735-L1738

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p22_descending_radiusPairSpectrum_zero_one :
    ∀ {c : ℝ} (hc : 4 < c),
    descending (radiusPairSpectrum c 0 1) = ![2, 0, -2, -2, -c] := by sorry
