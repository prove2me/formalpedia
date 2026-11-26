-- Prove2me | Theorems.Thm_EdenVerified_p22_descending_radiusPairSpectrum_two_two
-- name    : EdenVerified.p22_descending_radiusPairSpectrum_two_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:50:48.913211+00:00
-- url     : https://prove2.me/theorems/7c416f14-a6c5-53b8-a877-5b4b5891356c
-- title:
--   Eden Verified: p22 descending radius Pair Spectrum two two
-- statement:
--   The Eden Verified construction uses the p22 descending radius Pair Spectrum two two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1755-L1758
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1755-L1758

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p22_descending_radiusPairSpectrum_two_two :
    ∀ {c : ℝ} (hc : 4 < c),
    descending (radiusPairSpectrum c 2 2) = ![0, 0, -4, -4, -c] := by sorry
